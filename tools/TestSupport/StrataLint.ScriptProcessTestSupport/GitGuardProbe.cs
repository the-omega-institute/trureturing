using System.Diagnostics;
using System.Text.Json;
using System.Text.Json.Nodes;

namespace StrataLint.TestSupport;

// Experimental #8931 probe, deliberately limited to the implicated operation.
internal sealed class GitGuardProbe
{
    private const string Config = "core.autocrlf,core.safecrlf,core.filemode,core.ignorecase,core.preloadindex,core.fscache,core.fsmonitor,core.untrackedcache,core.checkstat,core.trustctime,core.splitindex,core.bigfilethreshold,core.symlinks,core.attributesfile,core.eol,core.sparsecheckout,index.version,index.threads,index.sparse,filter.*.clean,filter.*.process,filter.*.required";
    private readonly string trace;
    private readonly string prefix;
    private readonly string root;
    private object? baseline;
    private static int completed;
    private static int failures;
    private static int announced;

    private GitGuardProbe(ProcessStartInfo start)
    {
        root = start.WorkingDirectory;
        var directory = Path.Combine(TestRepositoryLayout.FindRoot(), "build/ci/logs/engineering/git-guard");
        Directory.CreateDirectory(directory);
        prefix = Path.Combine(directory, Environment.ProcessId + "-" + Guid.NewGuid().ToString("N"));
        trace = Path.Combine(Path.GetTempPath(), "git-guard-" + Guid.NewGuid().ToString("N") + ".jsonl");
        start.Environment["GIT_TRACE2_EVENT"] = trace;
        start.Environment["GIT_TRACE2_CONFIG_PARAMS"] = Config;
        start.Environment["GIT_TRACE2_ENV_VARS"] = "";
        if (Interlocked.Exchange(ref announced, 1) == 0)
        {
            // One aggregate write at host exit avoids racing shared-file writes or call-by-call console noise.
            AppDomain.CurrentDomain.ProcessExit += (_, _) => BestEffort(() => {
                var summary = JsonSerializer.Serialize(new { host_pid = Environment.ProcessId, completed, guard_expired = failures,
                    detail = "Per-call JSON retains native events and scale; failure JSON is pre-kill. An aborted host may lack this summary." });
                File.WriteAllText(Path.Combine(directory, Environment.ProcessId + "-summary.json"), summary);
                Console.WriteLine("GIT_GUARD_SUMMARY " + summary);
            });
            Console.WriteLine("GIT_GUARD_PROBE " + JsonSerializer.Serialize(new { host_pid = Environment.ProcessId,
                operation = "git add .", retention = directory, config_allowlist = Config,
                os = System.Runtime.InteropServices.RuntimeInformation.OSDescription, runtime = Environment.Version.ToString(), cpus = Environment.ProcessorCount,
                absent_config = "No explicit value reported by Git; Git version determines default.",
                discriminator = "Before kill: proc stat/HasExited versus exit task, native TRACE2 exit, drains and pressure." }));
        }
    }

    internal static GitGuardProbe? Start(ProcessStartInfo start)
    {
        if (start.FileName != "git" || !start.ArgumentList.SequenceEqual(new[] { "add", "." })) return null;
        try { return new GitGuardProbe(start); }
        catch (Exception error) { Console.WriteLine("GIT_GUARD_PROBE unavailable=" + error.GetType().Name); return null; }
    }

    internal void Started(Process process) => BestEffort(() => baseline = ProcessCancellationSnapshot.Baseline(process));

    internal void Failure(Process process, Task? exit, Task stdout, Task stderr, string phase)
    {
        BestEffort(() => {
            // Persist before the caller's existing kill/cleanup; no await or subprocess here.
            var snapshot = ProcessCancellationSnapshot.Capture(process, exit, stdout, stderr, phase);
            var events = Events();
            File.WriteAllText(prefix + ".failure.json", JsonSerializer.Serialize(new { root, baseline, scale = Scale(root), snapshot, trace2 = events }));
            Console.WriteLine("GIT_GUARD_FAILURE " + JsonSerializer.Serialize(new { artifact = prefix + ".failure.json", snapshot, trace2 = events }));
        });
    }

    internal void Finish(Process process, Task? exit, Task stdout, Task stderr, bool expired)
    {
        BestEffort(() => {
            File.WriteAllText(prefix + ".json", JsonSerializer.Serialize(new { root, baseline, scale = Scale(root), pid = process.Id,
                host_pid = Environment.ProcessId, guard_expired = expired,
                exit_task = exit?.Status.ToString(), stdout_task = stdout.Status.ToString(), stderr_task = stderr.Status.ToString(),
                child_exit = process.HasExited ? (int?)process.ExitCode : null, trace2 = Events() }));
            if (expired) Interlocked.Increment(ref failures); else Interlocked.Increment(ref completed);
        });
        BestEffort(() => File.Delete(trace));
    }

    private object Events()
    {
        // Never retain arbitrary argv, config values, paths in event payloads, or environment.
        var events = new List<JsonObject>();
        var unreadable = 0;
        var read = ProcessCancellationSnapshot.Observe(() => {
            foreach (var line in File.ReadLines(trace))
            {
                try
                {
                    var input = JsonNode.Parse(line)!.AsObject();
                    var kind = input["event"]?.GetValue<string>();
                    if (kind is not ("version" or "start" or "cmd_name" or "region_enter" or "region_leave" or "exit" or "atexit" or "child_start" or "child_exit" or "def_param")) continue;
                    var row = new JsonObject();
                    foreach (var key in new[] { "event", "sid", "thread", "time", "t_abs", "t_rel", "nesting", "category", "label", "code", "child_id", "pid", "exe", "name", "scope", "child_class", "use_shell" })
                        if (input[key] is { } value) row[key] = value.DeepClone();
                    if (kind == "def_param")
                    {
                        var key = input["param"]?.GetValue<string>() ?? "";
                        if (!Config.Split(',').Contains(key, StringComparer.OrdinalIgnoreCase)
                            && !(key.StartsWith("filter.", StringComparison.Ordinal) && new[] { ".clean", ".process", ".required" }.Any(suffix => key.EndsWith(suffix, StringComparison.Ordinal)))) continue;
                        row["param"] = key;
                        var value = input["value"]?.GetValue<string>() ?? "";
                        row["value"] = SafeConfig(value);
                    }
                    if (kind == "child_start") row["argv"] = "REDACTED; child_id correlates child_exit and proc children";
                    if (kind == "start") row["argv"] = "REDACTED; observed parent command is git add .";
                    events.Add(row);
                }
                catch (JsonException) { unreadable++; }
            }
            return "read";
        });
        return new { read, incomplete_lines = unreadable, events };
    }

    private static string SafeConfig(string value) => value is "true" or "false" or "input" or "warn" or "default" or "minimal"
        || (value.Length > 0 && value.Length <= 16 && value.All(char.IsAsciiDigit)) ? value : "SET-REDACTED";

    private static object Scale(string root)
    {
        long bytes = 0;
        var files = 0;
        var gitFiles = 0;
        var state = ProcessCancellationSnapshot.Observe(() => {
            var pending = new Stack<string>();
            pending.Push(root);
            while (pending.TryPop(out var directory))
                foreach (var entry in new DirectoryInfo(directory).EnumerateFileSystemInfos())
                {
                    if ((entry.Attributes & FileAttributes.ReparsePoint) != 0) continue;
                    if (entry is DirectoryInfo)
                    {
                        if (entry.Name is not ("build" or "bin" or "obj" or ".lake")) pending.Push(entry.FullName);
                    }
                    else if (entry.FullName.StartsWith(Path.Combine(root, ".git") + Path.DirectorySeparatorChar, StringComparison.Ordinal)) gitFiles++;
                    else { files++; bytes += ((FileInfo)entry).Length; }
                }
            return "counted; excludes build/bin/obj/.lake and symlinks; .git counted separately";
        });
        return new { files, bytes, git_files = gitFiles, state };
    }

    private static void BestEffort(Action action)
    {
        try { action(); }
        catch (Exception error) { Console.WriteLine("GIT_GUARD_PROBE unavailable=" + error.GetType().Name); }
    }
}
