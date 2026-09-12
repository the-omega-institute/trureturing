using System.Text;
using System.Runtime.Versioning;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class MakeWorkflowTests
{
    [Theory]
    [InlineData("")]
    [InlineData("Blueprint/D5/Probe.md")]
    [InlineData("docs/develop/notes.md")]
    [InlineData("Golden/values-kernels.toml")]
    [UnsupportedOSPlatform("windows")]
    public void CurrentScribeRunsEveryConsistencyCheckWithoutGitOrBase(string changedPath)
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
        File.WriteAllText(report, "candidate report");
        File.WriteAllText(dll, "candidate binary");
        WriteExecutable(Path.Combine(bin, "git"), "#!/bin/bash\nexit 93\n");
        WriteExecutable(Path.Combine(bin, "dotnet"), "#!/bin/bash\nprintf '%s\\n' \"$*\" >> \"$SCRIBE_LOG\"\n");
        ProcessOutput Run(params string[] selection) => TestProcessRunner.Run("/usr/bin/env",
            [$"PATH={bin}:/usr/bin:/bin", $"SCRIBE_LOG={log}", "BASE=unavailable",
             "/bin/bash", script, report, dll, .. selection], root, BoundedProcessRunner.HangDetectionBudget, 64 * 1024);
        var result = Run();
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardError));
        Assert.Equal(new[]
        {
            $"{dll} projections --check --report {report}",
            $"{dll} describe-report --check",
            $"{dll} markdown-check --report {report}",
        }, File.ReadAllLines(log));
        foreach (var invalid in new[] { new string('a', 40), root, "" })
        {
            var rejected = Run(invalid);
            Assert.True(rejected.ExitCode == 2, Encoding.UTF8.GetString(rejected.StandardError));
            Assert.Contains("PATHS_FILE must be a readable regular file", Encoding.UTF8.GetString(rejected.StandardError), StringComparison.Ordinal);
            Assert.Equal(3, File.ReadAllLines(log).Length);
        }
        var paths = Path.Combine(root, "selected paths.txt");
        File.WriteAllText(paths, "Blueprint/D5/Probe.md\n");
        var selected = Run(paths);
        Assert.True(selected.ExitCode == 0, Encoding.UTF8.GetString(selected.StandardError));
        Assert.Equal(new[]
        {
            $"{dll} projections --check --report {report}",
            $"{dll} describe-report --check",
            $"{dll} markdown-check --report {report} --paths-from {paths}",
        }, File.ReadAllLines(log).Skip(3));
    }
}
