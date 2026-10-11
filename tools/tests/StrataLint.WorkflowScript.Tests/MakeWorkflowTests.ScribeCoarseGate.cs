using StrataLint.Runtime;
using static StrataLint.TestSupport.TestExecutable;
using System.Text;
using System.Runtime.Versioning;
using StrataLint.Engine;

namespace StrataLint.WorkflowScript.Tests;

public sealed partial class MakeWorkflowTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    [UnsupportedOSPlatform("windows")]
    public void ScribeEmitPassesCallerChangesOrExplicitManifestToItsOwnHost(bool explicitPaths)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var root = Path.Combine(temporary.Path, "repository with spaces");
        Directory.CreateDirectory(root);
        var script = Path.Combine(root, ScribeScriptPath);
        Directory.CreateDirectory(Path.GetDirectoryName(script)!);
        File.Copy(Path.Combine(TestRepositoryLayout.FindRoot(), ScribeScriptPath), script);
        WriteExecutable(Path.Combine(root, "tools/scripts/report/report-consumer.sh"),
            "#!/bin/bash\nwhile [[ \"$1\" != -- ]]; do shift; done\nshift\nexec \"$@\"\n");
        var bin = Path.Combine(root, "bin");
        var calls = Path.Combine(root, "calls");
        var selected = Path.Combine(root, "selected");
        WriteExecutable(Path.Combine(bin, "git"), """
            #!/bin/bash
            if [[ "$1" == diff ]]; then
              printf 'Blueprint/D5/Changed.scribe.cs\0'
            elif [[ "$1" == ls-files ]]; then
              printf 'Blueprint/D5/New file.scribe.cs\0'
            else
              exit 93
            fi
            """);
        WriteExecutable(Path.Combine(bin, "dotnet"), """
            #!/bin/bash
            printf '%s\n' "$*" >> "$SCRIBE_LOG"
            if [[ "$*" == *' lean-inputs '* ]]; then printf 'D5.Changed\n'; fi
            while [[ "$#" -gt 0 ]]; do
              if [[ "$1" == --paths-from ]]; then cat "$2" > "$SELECTED_LOG"; break; fi
              shift
            done
            """);
        WriteExecutable(Path.Combine(bin, "make"), "#!/bin/bash\nprintf 'make:%s\\n' \"$*\" >> \"$SCRIBE_LOG\"\n");
        var manifest = Path.Combine(root, "caller paths");
        File.WriteAllText(manifest, "Blueprint/D5/Explicit.scribe.cs\0");
        var result = TestProcessRunner.Run("/usr/bin/env",
            [$"PATH={bin}:/usr/bin:/bin", $"SCRIBE_LOG={calls}", $"SELECTED_LOG={selected}",
             "BASE=fixed-base", $"PATHS={(explicitPaths ? manifest : "")}",
             "/bin/bash", script, "emit"], temporary.Path, BoundedProcessRunner.HangDetectionBudget, 64 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        var invocations = File.ReadAllLines(calls);
        Assert.Equal(5, invocations.Length);
        Assert.Contains("tools/StrataLint.Scribe/StrataLint.Scribe.csproj", invocations[0], StringComparison.Ordinal);
        Assert.Contains("lean-inputs --paths-from", invocations[1], StringComparison.Ordinal);
        Assert.Equal("make:lean-report-scoped LEAN_TARGETS=D5.Changed", invocations[2]);
        Assert.Contains("emit --paths-from", invocations[3], StringComparison.Ordinal);
        Assert.Contains("--scoped", invocations[3], StringComparison.Ordinal);
        Assert.EndsWith("emit-values", invocations[4], StringComparison.Ordinal);
        Assert.Equal(explicitPaths ? new[] { "Blueprint/D5/Explicit.scribe.cs" }
            : new[] { "Blueprint/D5/Changed.scribe.cs", "Blueprint/D5/New file.scribe.cs" },
            File.ReadAllText(selected).Split('\0', StringSplitOptions.RemoveEmptyEntries));
    }

    [Theory]
    [InlineData("")]
    [InlineData("Blueprint/D5/Probe.md")]
    [InlineData("docs/develop/notes.md")]
    [InlineData("Golden/values-kernels.toml")]
    [UnsupportedOSPlatform("windows")]
    public void CurrentScribeRunsContentChecksInOneProcessWithoutGitOrBase(string changedPath)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var root = temporary.Path;
        var script = Path.Combine(root, ScribeContentChecksScriptPath);
        Directory.CreateDirectory(Path.GetDirectoryName(script)!);
        File.Copy(Path.Combine(TestRepositoryLayout.FindRoot(), ScribeContentChecksScriptPath), script);
        if (changedPath.Length > 0)
        {
            var changed = Path.Combine(root, changedPath);
            Directory.CreateDirectory(Path.GetDirectoryName(changed)!);
            File.WriteAllText(changed, "candidate input\n");
        }
        var bin = Path.Combine(root, "bin");
        var log = Path.Combine(root, "calls");
        var report = Path.Combine(root, "report.json");
        var dll = Path.Combine(root, "scribe.dll");
        var paths = Path.Combine(root, "selected paths.txt");
        File.WriteAllText(report, "candidate report");
        File.WriteAllText(dll, "candidate binary");
        File.WriteAllText(paths, changedPath.Length > 0 ? changedPath + "\0" : string.Empty);
        WriteExecutable(Path.Combine(bin, "git"), "#!/bin/bash\nexit 93\n");
        WriteExecutable(Path.Combine(bin, "dotnet"), "#!/bin/bash\nprintf '%s\\n' \"$*\" >> \"$SCRIBE_LOG\"\n");
        ProcessOutput Run(params string[] selection) => TestProcessRunner.Run("/usr/bin/env",
            [$"PATH={bin}:/usr/bin:/bin", $"SCRIBE_LOG={log}", "BASE=unavailable",
             "/bin/bash", script, report, dll, .. selection], root, BoundedProcessRunner.HangDetectionBudget, 64 * 1024);
        var result = Run(paths);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        Assert.StartsWith($"{dll} content-check --report {report} --paths-from ", Assert.Single(File.ReadAllLines(log)));
        foreach (var invalid in new[] { new string('a', 40), root, "" })
        {
            var rejected = Run(invalid);
            Assert.True(rejected.ExitCode == 2, Encoding.UTF8.GetString(rejected.StandardError));
            Assert.Contains("PATHS_FILE must be a readable regular file", Encoding.UTF8.GetString(rejected.StandardError), StringComparison.Ordinal);
            Assert.Single(File.ReadAllLines(log));
        }
        File.WriteAllText(paths, "Blueprint/D5/Probe.md\0");
        var selected = Run(paths);
        Assert.True(selected.ExitCode == 0, Encoding.UTF8.GetString(selected.StandardError));
        Assert.Equal(new[]
        {
            $"{dll} content-check --report {report} --paths-from {paths}",
        }, File.ReadAllLines(log).Skip(1));
    }

    [Theory]
    [InlineData(1)]
    [InlineData(2)]
    [InlineData(29)]
    [UnsupportedOSPlatform("windows")]
    public void ScribeContentChecksPreserveChildOutputAndExitCode(int childExit)
    {
        if (OperatingSystem.IsWindows()) return;
        using var root = new TemporaryDirectory();
        var bin = Path.Combine(root.Path, "bin");
        var report = Path.Combine(root.Path, "report.json");
        var dll = Path.Combine(root.Path, "scribe.dll");
        var paths = Path.Combine(root.Path, "selected paths");
        File.WriteAllText(report, "candidate report");
        File.WriteAllText(dll, "candidate binary");
        File.WriteAllText(paths, string.Empty);
        WriteExecutable(Path.Combine(bin, "dotnet"),
            "#!/bin/bash\nprintf 'check output\\n'\nprintf 'check error\\n' >&2\nexit \"$CHILD_EXIT\"\n");
        var result = TestProcessRunner.Run("/usr/bin/env",
            [$"PATH={bin}:/usr/bin:/bin", $"CHILD_EXIT={childExit}", "/bin/bash",
             Path.Combine(TestRepositoryLayout.FindRoot(), ScribeContentChecksScriptPath), report, dll, paths],
            root.Path, BoundedProcessRunner.HangDetectionBudget, 64 * 1024);
        Assert.Equal(childExit, result.ExitCode);
        Assert.Equal("check output\n", Encoding.UTF8.GetString(result.StandardOutput));
        Assert.Equal("check error\n", Encoding.UTF8.GetString(result.StandardError));
    }
}
