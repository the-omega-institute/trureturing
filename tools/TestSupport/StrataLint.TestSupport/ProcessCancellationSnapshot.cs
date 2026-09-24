using System.Diagnostics;

namespace StrataLint.TestSupport;

// Disposable #8931 observation. Reads only; never decides a process/test outcome.
internal static class ProcessCancellationSnapshot
{
    public static object Baseline(Process process) => new {
        uptime = Observe(() => File.ReadAllText("/proc/uptime")),
        stat = Observe(() => File.ReadAllText($"/proc/{process.Id}/stat")),
        io = Observe(() => File.ReadAllText($"/proc/{process.Id}/io")),
        cpu_pressure = Observe(() => File.ReadAllText("/proc/pressure/cpu")),
        io_pressure = Observe(() => File.ReadAllText("/proc/pressure/io")),
        memory_pressure = Observe(() => File.ReadAllText("/proc/pressure/memory")) };

    public static object Capture(Process process, Task? exit, Task stdout, Task stderr, string phase)
    {
        ThreadPool.GetAvailableThreads(out var workers, out var io);
        ThreadPool.GetMaxThreads(out var maxWorkers, out var maxIo);
        var exitState = exit?.Status.ToString() ?? "not-created";
        var stdoutState = stdout.Status.ToString();
        var stderrState = stderr.Status.ToString();
        var pool = new { threads = ThreadPool.ThreadCount, pending = ThreadPool.PendingWorkItemCount,
            completed = ThreadPool.CompletedWorkItemCount, available_workers = workers, available_io = io, max_workers = maxWorkers, max_io = maxIo };
        var readings = new Dictionary<string, string>();
        void Read(string path) => readings[path] = Observe(() => File.ReadAllText(path));
        // Read native identity/state before HasExited (which may reap an exited child).
        readings["uptime_before"] = Observe(() => File.ReadAllText("/proc/uptime"));
        void Pid(int pid)
        {
            foreach (var name in new[] { "stat", "status", "wchan", "schedstat", "io", $"task/{pid}/children" })
                Read($"/proc/{pid}/{name}");
        }
        Pid(process.Id);
        var hasExited = Observe(() => process.HasExited.ToString());
        var children = readings[$"/proc/{process.Id}/task/{process.Id}/children"];
        foreach (var child in children.Split(' ', StringSplitOptions.RemoveEmptyEntries).Take(32))
            if (int.TryParse(child.Trim(), out var pid)) Pid(pid);
        if (process.Id != Environment.ProcessId) Pid(Environment.ProcessId);
        foreach (var path in new[] { "/proc/loadavg", "/proc/pressure/cpu", "/proc/pressure/io", "/proc/pressure/memory", "/proc/self/cgroup" }) Read(path);
        readings["/proc/stat:selected"] = Observe(() => string.Join('\n', File.ReadLines("/proc/stat").Where(line =>
            line.StartsWith("cpu ", StringComparison.Ordinal) || line.StartsWith("ctxt ", StringComparison.Ordinal) || line.StartsWith("procs_", StringComparison.Ordinal))));
        readings["/proc/meminfo:selected"] = Observe(() => string.Join('\n', File.ReadLines("/proc/meminfo").Where(line =>
            line.StartsWith("MemTotal:", StringComparison.Ordinal) || line.StartsWith("MemAvailable:", StringComparison.Ordinal) || line.StartsWith("SwapFree:", StringComparison.Ordinal))));
        var group = readings["/proc/self/cgroup"].Split('\n').FirstOrDefault(line => line.StartsWith("0::/", StringComparison.Ordinal));
        if (group is not null)
        {
            var root = Path.GetFullPath("/sys/fs/cgroup/" + group[4..]);
            if (root == "/sys/fs/cgroup" || root.StartsWith("/sys/fs/cgroup/", StringComparison.Ordinal))
                foreach (var name in new[] { "cpu.stat", "cpu.max", "cpu.pressure", "io.stat", "io.pressure", "memory.current", "memory.events", "memory.pressure" }) Read(root + "/" + name);
        }
        readings["uptime_after"] = Observe(() => File.ReadAllText("/proc/uptime"));
        return new { observation = "before-kill", phase, pid = process.Id, host_pid = Environment.ProcessId,
            has_exited = hasExited, exit_task = exitState, stdout_task = stdoutState, stderr_task = stderrState, thread_pool = pool,
            readings, limitation = "Sequential catch-time sample; not atomic or nominal deadline-time. Missing proc data is not proof of exit." };
    }

    public static string Observe(Func<string> read)
    {
        try { return read(); }
        catch (Exception error) { return "UNAVAILABLE:" + error.GetType().Name; }
    }
}
