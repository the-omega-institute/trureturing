using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class LeanInspectorScriptTests
{
    private const string InspectorScript = "tools/lean-inspector/inspect.sh";
    private const string InspectorSource = "tools/lean-inspector/Inspector.lean";
    private const string MaterialCompactor = "tools/lean-inspector/materials.py";
    private const string InputScript = "tools/scripts/report/lean-report-input.sh";
    private const string ResourceObservationLibrary = "tools/scripts/lib/resource-observation-lib.sh";
    private const string CacheRunScript = "tools/scripts/worktree/lean-cache-run.sh";

    [Fact]
    public void InspectorDefaultsToCompleteModuleEnumeration()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var root = TestRepositoryLayout.FindRoot();
        var repository = Path.Combine(temporary.Path, "repo");
        Directory.CreateDirectory(Path.Combine(repository, "D5"));
        Directory.CreateDirectory(Path.Combine(repository, "tools", "lean-inspector"));
        Directory.CreateDirectory(Path.Combine(repository, "tools", "scripts", "report"));
        Write(repository, "Trureturing.lean", "import D5.Probe\n");
        Write(repository, "D5/Probe.lean", "def probe : Nat := 1\n");
        foreach (var relative in new[]
        {
            InspectorScript,
            InspectorSource,
            MaterialCompactor,
            InputScript,
            ResourceObservationLibrary,
        })
        {
            Directory.CreateDirectory(Path.GetDirectoryName(Path.Combine(repository, relative))!);
            File.Copy(Path.Combine(root, relative), Path.Combine(repository, relative));
        }
        InstallCacheRun(repository);
        var lake = Path.Combine(temporary.Path, "lake");
        File.WriteAllText(lake, "#!/usr/bin/env bash\nprintf '%s\\n' \"$*\" >> \"$STUB_LOG\"\nif [[ \"$*\" == *' --output '* ]]; then while [[ $# -gt 0 ]]; do [[ $1 == --output ]] && { printf '{\"modules\": [], \"schema\": \"stratalint-lean-inspector-spool-v1\"}\\n' > \"$2\"; break; }; shift; done; fi\n", new UTF8Encoding(false));
        File.SetUnixFileMode(lake, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var log = Path.Combine(temporary.Path, "lake.log");
        var output = Path.Combine(temporary.Path, "report.json");

        var full = Run("env", [$"LAKE_BIN={lake}", $"STUB_LOG={log}", Path.Combine(repository, InspectorScript), "--repository", repository, "--output", output], repository);
        Assert.Equal(0, full.ExitCode);
        var fullInspect = File.ReadAllLines(log).Single(static line => line.Contains(" --output ", StringComparison.Ordinal));
        Assert.Contains("Trureturing Trureturing.lean sha256:", fullInspect, StringComparison.Ordinal);
        Assert.Contains("D5.Probe D5/Probe.lean sha256:", fullInspect, StringComparison.Ordinal);
    }

    [Fact]
    public void ProducerDoesNotExecuteCandidateModuleEnumerator()
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var root = TestRepositoryLayout.FindRoot();
        var repository = Path.Combine(temporary.Path, "repo");
        Directory.CreateDirectory(Path.Combine(repository, "D5"));
        Write(repository, "Trureturing.lean", "import D5.Probe\n");
        Write(repository, "D5/Probe.lean", "def probe : Nat := 1\n");
        var marker = Path.Combine(temporary.Path, "candidate-helper-ran");
        var poisoned = Path.Combine(repository, InputScript);
        Directory.CreateDirectory(Path.GetDirectoryName(poisoned)!);
        File.WriteAllText(
            poisoned,
            $"#!/usr/bin/env bash\ntouch '{marker}'\nprintf 'Trureturing\\tTrureturing.lean\\n'\n",
            new UTF8Encoding(false));
        File.SetUnixFileMode(poisoned, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        InstallCacheRun(repository);
        var lake = Path.Combine(temporary.Path, "lake");
        File.WriteAllText(lake, "#!/usr/bin/env bash\nif [[ \"$*\" == *' --output '* ]]; then while [[ $# -gt 0 ]]; do [[ $1 == --output ]] && { printf '{\"modules\": [], \"schema\": \"stratalint-lean-inspector-spool-v1\"}\\n' > \"$2\"; break; }; shift; done; fi\n", new UTF8Encoding(false));
        File.SetUnixFileMode(lake, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);

        var result = Run("env", [$"LAKE_BIN={lake}", Path.Combine(root, InspectorScript), "--repository", repository, "--output", Path.Combine(temporary.Path, "report.json")], repository);

        Assert.Equal(0, result.ExitCode);
        Assert.False(File.Exists(marker), "producer executed the candidate-owned module enumerator");
    }

    private static ProcessOutput Run(string command, IReadOnlyList<string> arguments, string cwd) =>
        TestProcessRunner.Run(command, arguments, cwd, BoundedProcessRunner.HangDetectionBudget, 1024 * 1024);

    private static void Write(string root, string relative, string contents)
    {
        var path = Path.Combine(root, relative);
        Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        File.WriteAllText(path, contents, new UTF8Encoding(false));
    }

    private static void InstallCacheRun(string repository)
    {
        if (OperatingSystem.IsWindows()) return;
        Write(repository, CacheRunScript, "#!/usr/bin/env bash\nexec \"$@\"\n");
        File.SetUnixFileMode(
            Path.Combine(repository, CacheRunScript),
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
    }

}
