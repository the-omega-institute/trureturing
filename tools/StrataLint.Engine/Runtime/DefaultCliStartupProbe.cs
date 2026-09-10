using System.ComponentModel;
using System.Diagnostics;
using System.Reflection.Metadata;
using System.Runtime.InteropServices;
using System.Security.Cryptography;
using System.Text.Json;

namespace StrataLint.Engine;

// Disposable #6769 diagnostic. No observation participates in a verdict or a budget.
internal sealed class DefaultCliStartupProbe(string invocation, string role, Action<string> write)
{
    internal const string PathVariable = "STRATALINT_STARTUP_PROBE_PATH";
    internal const string InvocationVariable = "STRATALINT_STARTUP_PROBE_INVOCATION";
    internal const string Prefix = "DEFAULT_CLI_STARTUP_PROBE ";
    internal static readonly AsyncLocal<DefaultCliStartupProbe?> Current = new();
    private readonly Dictionary<string, int> calls = new()
    {
        ["report-file-read"] = 0, ["scribe-verify"] = 0, ["scribe-discover"] = 0,
    };
    private int sequence;
    private string? childPath;

    internal static void EnterChild(long mainEntry)
    {
        var path = Environment.GetEnvironmentVariable(PathVariable);
        var name = Environment.GetEnvironmentVariable(InvocationVariable);
        if (string.IsNullOrEmpty(path) || string.IsNullOrEmpty(name)) return;
        var probe = new DefaultCliStartupProbe(name, "child", line => File.AppendAllText(path, line + "\n"))
        {
            childPath = path,
        };
        Current.Value = probe;
        probe.Mark("main-entry", timestamp: mainEntry);
        probe.Runtime();
        probe.Resources("main-entry");
    }

    internal void Mark(string phase, object? data = null, long? timestamp = null)
    {
        var line = JsonSerializer.Serialize(new
        {
            protocol = 1, invocation, role, sequence = ++sequence,
            pid = Environment.ProcessId, phase,
            timestamp = timestamp ?? TimeProvider.System.GetTimestamp(),
            frequency = TimeProvider.System.TimestampFrequency, data,
        });
        try { write(Prefix + line); }
        catch (Exception error) when (ObservationError(error))
        {
            // If file output fails, stderr is the last available observation channel.
            Emit(Console.Error.WriteLine, Prefix + JsonSerializer.Serialize(new
            {
                protocol = 1, invocation, role, phase = "observation-unavailable",
                operation = phase, error = error.GetType().Name,
            }));
        }
    }

    internal void Count(string name)
    {
        calls[name]++;
        Mark("call", new { name, count = calls[name] });
    }

    internal void Complete()
    {
        Mark("call-counts", calls);
        Resources("before-exit");
        Mark("child-cpu-before-exit", Observe(() =>
        {
            using var self = Process.GetCurrentProcess();
            return new { self_cpu_ms = self.TotalProcessorTime.TotalMilliseconds };
        }));
        Mark("main-finally-end");
    }

    internal void Runtime() => Mark("runtime", new
    {
        framework = RuntimeInformation.FrameworkDescription,
        target_framework = AppContext.TargetFrameworkName,
        os = RuntimeInformation.OSDescription,
        os_architecture = RuntimeInformation.OSArchitecture.ToString(),
        process_architecture = RuntimeInformation.ProcessArchitecture.ToString(),
        engine_mvid = typeof(DefaultCliStartupProbe).Module.ModuleVersionId,
    });

    internal void ProcessState(string phase, Process process) => Mark(phase, Observe(() =>
    {
        var exited = process.HasExited;
        return new { child_pid = process.Id, has_exited = exited, exit_code = exited ? (int?)process.ExitCode : null };
    }));

    internal void ConfigureGit(ProcessStartInfo startInfo)
    {
        if (childPath is null || startInfo.FileName != "git") return;
        startInfo.Environment["GIT_TRACE2_EVENT"] = childPath + ".git";
        // Trace only command events, never configured environment/config values.
        startInfo.Environment["GIT_TRACE2_ENV_VARS"] = "";
        startInfo.Environment["GIT_TRACE2_CONFIG_PARAMS"] = "";
    }

    internal void Resources(string boundary)
    {
        var begin = TimeProvider.System.GetTimestamp();
        var data = new Dictionary<string, object?>();
        data["self"] = Observe(() =>
        {
            using var self = Process.GetCurrentProcess();
            return new { cpu_ms = self.TotalProcessorTime.TotalMilliseconds, rss_bytes = self.WorkingSet64 };
        });
        if (OperatingSystem.IsLinux())
        {
            foreach (var path in new[] { "/proc/stat", "/proc/meminfo", "/proc/pressure/cpu", "/proc/pressure/memory", "/proc/pressure/io" })
                data[path] = Observe(() => path == "/proc/stat"
                    ? string.Join("\n", File.ReadLines(path).Where(line => line.StartsWith("cpu ", StringComparison.Ordinal)
                        || line.StartsWith("procs_", StringComparison.Ordinal)))
                    : File.ReadAllText(path));
            var cgroup = Observe(() => File.ReadLines("/proc/self/cgroup")
                .FirstOrDefault(line => line.StartsWith("0::", StringComparison.Ordinal))?[3..]
                ?? "UNAVAILABLE:no-unified-cgroup");
            data["cgroup_v2_path"] = cgroup;
            if (cgroup is string group && group.StartsWith('/'))
            {
                // Standard Linux cgroup v2 mount; other layouts report unavailable.
                var directory = Path.Combine("/sys/fs/cgroup", group.TrimStart('/'));
                foreach (var name in new[] { "cpu.stat", "cpu.max", "cpuset.cpus.effective", "cpu.pressure",
                    "memory.current", "memory.peak", "memory.max", "memory.events", "memory.pressure", "io.pressure" })
                    data[name] = Observe(() => File.ReadAllText(Path.Combine(directory, name)));
            }
        }
        else data["linux"] = "UNAVAILABLE:not-linux";
        Mark("resources", new { boundary, begin, end = TimeProvider.System.GetTimestamp(), observations = data });
    }

    internal void Fixture(string root) => Mark("fixture", Observe(() =>
    {
        var files = Directory.GetFiles(root, "*", SearchOption.AllDirectories)
            .Where(path => !Path.GetRelativePath(root, path).StartsWith(".git/", StringComparison.Ordinal)).ToArray();
        return new { files = files.Length, bytes = files.Sum(path => new FileInfo(path).Length),
            scribe_files = files.Count(path => path.EndsWith(".scribe.cs", StringComparison.Ordinal)) };
    }));

    internal void Cleanup(string path)
    {
        foreach (var file in new[] { path, path + ".git" })
            Mark("trace-cleanup", Observe(() => { File.Delete(file); return "deleted-or-absent"; }));
    }

    // Called after the measured invocation: hashes do not warm its binaries before start.
    internal void Identities(string directory)
    {
        Mark("binary-identities", Observe(() => Directory.GetFiles(directory)
            .Where(path => Path.GetFileName(path).StartsWith("StrataLint", StringComparison.Ordinal)
                || Path.GetFileName(path).StartsWith("Trureturing.Truth", StringComparison.Ordinal))
            .Where(path => Path.GetExtension(path) is ".dll" or ".pdb" or ".json" or "" or ".exe")
            .Order(StringComparer.Ordinal)
            .Select(path => new { file = Path.GetFileName(path), identity = Observe(() =>
            {
                using var stream = File.OpenRead(path);
                return new { bytes = stream.Length, sha256 = Convert.ToHexStringLower(SHA256.HashData(stream)) };
            }) }).ToArray()));
        // Portable PDB checksums bind the measured binaries to the diagnostic sources,
        // including CI's mapped paths. No checkout traversal or repository subprocess.
        foreach (var pdb in new[] { "StrataLint.pdb", "StrataLint.Engine.pdb", "StrataLint.Scribe.pdb", "StrataLint.Tests.pdb" })
            Mark("source-checksums", Observe(() =>
            {
                using var stream = File.OpenRead(Path.Combine(directory, pdb));
                using var provider = MetadataReaderProvider.FromPortablePdbStream(stream);
                var reader = provider.GetMetadataReader();
                return reader.Documents.Select(handle => reader.GetDocument(handle))
                    .Select(document => new { path = reader.GetString(document.Name),
                        algorithm = reader.GetGuid(document.HashAlgorithm),
                        checksum = Convert.ToHexStringLower(reader.GetBlobBytes(document.Hash)) })
                    .Where(document => Path.GetFileName(document.path) is "DefaultCliStartupProbe.cs" or "DefaultCliStartupTests.cs"
                        or "Program.cs" or "DigestStatusCommand.cs" or "BoundedProcessRunner.cs"
                        or "GitRepositorySnapshotReader.cs" or "RawLeanReportArtifact.cs"
                        or "ScribeEmissionVerifier.cs" or "DocumentDefinitions.cs").ToArray();
            }));
    }

    internal void Collect(string path, Action<string> emit)
    {
        Mark("child-trace-collection", Observe(() =>
        {
            var lines = File.ReadAllLines(path);
            foreach (var line in lines) Emit(emit, line);
            return new { lines = lines.Length };
        }));
        Mark("git-trace-collection", Observe(() =>
        {
            var count = 0;
            foreach (var line in File.ReadLines(path + ".git"))
            {
                using var document = JsonDocument.Parse(line);
                var value = document.RootElement;
                if (value.GetProperty("event").GetString() is not ("version" or "start" or "exit" or "atexit")) continue;
                var fields = new Dictionary<string, JsonElement>();
                foreach (var key in new[] { "event", "sid", "time", "t_abs", "code", "exe" })
                    if (value.TryGetProperty(key, out var field)) fields[key] = field;
                Mark("git-trace2", fields);
                count++;
            }
            return new { events = count };
        }));
    }

    private static object Observe(Func<object> read)
    {
        try { return read(); }
        catch (Exception error) when (ObservationError(error) || error is JsonException or BadImageFormatException)
        { return new { unavailable = error.GetType().Name }; }
    }

    internal static void Emit(Action<string> emit, string line)
    {
        try { emit(line); }
        catch (Exception error) when (ObservationError(error))
        {
            // Output itself is unavailable; functional exceptions are never handled here.
            System.Diagnostics.Debug.WriteLine("startup probe output unavailable: " + error.GetType().Name);
        }
    }

    private static bool ObservationError(Exception error) => error is IOException or UnauthorizedAccessException
        or System.Security.SecurityException or Win32Exception or InvalidOperationException or NotSupportedException;
}
