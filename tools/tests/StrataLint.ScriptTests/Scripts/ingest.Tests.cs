using StrataLint.Engine;
using System.Text.RegularExpressions;

namespace StrataLint.ScriptTests;

[ScriptSubject("tools/scripts/ingest.sh")]
public sealed class IngestScriptTests
{
    private const string IngestScriptPath = "tools/scripts/ingest.sh";
    private const string LeanReportInputScriptPath = "tools/scripts/report/lean-report-input.sh";

    [Fact]
    public void IngestWrapperSeparatesReportFreeDigestionFromTruthAlignment()
    {
        var script = File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/ingest.sh"));

        Assert.Contains("lean-report-input.sh", script, StringComparison.Ordinal);
        Assert.Contains(" address --repository ", script, StringComparison.Ordinal);
        Assert.Contains("git -C \"$ROOT\" archive", script, StringComparison.Ordinal);
        Assert.DoesNotContain(
            "input_state=\"$(report_input_state)\"",
            script,
            StringComparison.Ordinal);
        Assert.Contains("report_input_state\n    cleanup", script, StringComparison.Ordinal);
        Assert.Contains(
            "ingest --base \"$BASE\" --report-input-state \"$REPORT_INPUT_STATE\"",
            script,
            StringComparison.Ordinal);
        Assert.Contains("align-digestion-status)", script, StringComparison.Ordinal);
        Assert.Contains(
            "--role digestion-alignment-consumer --report \"$REPORT\"",
            script,
            StringComparison.Ordinal);
        Assert.Single(Regex.Matches(script, Regex.Escape("exec \"$CONSUMER\"")).Cast<Match>());
    }

    [Fact]
    public void IngestWrapperDerivesReportInputStateFromExecutableClosureDelta()
    {
        if (OperatingSystem.IsWindows()) return;

        const string leanSource = "theorem probe : True := by trivial\n";
        var root = TestRepositoryLayout.FindRoot();
        using var fixture = new TemporaryDirectory();
        var binDirectory = Path.Combine(fixture.Path, "bin");
        var ingestPath = Path.Combine(fixture.Path, IngestScriptPath);
        var inputPath = Path.Combine(fixture.Path, LeanReportInputScriptPath);
        Directory.CreateDirectory(binDirectory);
        Directory.CreateDirectory(Path.GetDirectoryName(ingestPath)!);
        Directory.CreateDirectory(Path.GetDirectoryName(inputPath)!);
        Directory.CreateDirectory(Path.Combine(fixture.Path, "D5"));
        Directory.CreateDirectory(Path.Combine(fixture.Path, "tools", "StrataLint.Cli"));
        File.Copy(Path.Combine(root, IngestScriptPath), ingestPath);
        File.Copy(Path.Combine(root, LeanReportInputScriptPath), inputPath);
        File.WriteAllText(Path.Combine(fixture.Path, "Trureturing.lean"), "import D5.Probe\n");
        File.WriteAllText(Path.Combine(fixture.Path, "D5", "Probe.lean"), leanSource);
        File.WriteAllText(Path.Combine(fixture.Path, "lean-toolchain"), "leanprover/lean4:v4.31.0\n");
        File.WriteAllText(Path.Combine(fixture.Path, "lake-manifest.json"), "{\"version\":\"1.1.0\"}\n");
        File.WriteAllText(Path.Combine(fixture.Path, "lakefile.toml"), "name = \"Fixture\"\n");
        File.WriteAllText(Path.Combine(fixture.Path, "README.md"), "baseline\n");
        var dotnetPath = Path.Combine(binDirectory, "dotnet");
        File.WriteAllText(
            dotnetPath,
            """
            #!/usr/bin/env bash
            if [[ "${1:-}" == "msbuild" ]]; then exit 1; fi
            printf '%s\n' "$*"
            """ + "\n");
        foreach (var executable in new[] { ingestPath, inputPath, dotnetPath })
        {
            File.SetUnixFileMode(
                executable,
                UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        }

        ReviewRegressionTests.RunGit(fixture.Path, "init", "--quiet");
        ReviewRegressionTests.RunGit(fixture.Path, "config", "user.email", "stratalint@example.invalid");
        ReviewRegressionTests.RunGit(fixture.Path, "config", "user.name", "StrataLint Tests");
        ReviewRegressionTests.RunGit(fixture.Path, "add", ".");
        ReviewRegressionTests.RunGit(fixture.Path, "commit", "--quiet", "-m", "ingest wrapper fixture");

        ProcessOutput RunWrapper() => TestProcessRunner.Run(
            "/bin/bash",
            [
                "-c",
                "PATH=\"$1:$PATH\" XDG_CACHE_HOME=\"$2\" exec \"$3\" ingest HEAD",
                "ingest-wrapper",
                binDirectory,
                Path.Combine(fixture.Path, "cache"),
                ingestPath,
            ],
            fixture.Path,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);

        File.AppendAllText(Path.Combine(fixture.Path, "D5", "Probe.lean"), "-- closure delta\n");
        var changed = RunWrapper();
        Assert.Equal(0, changed.ExitCode);
        Assert.Contains(
            "ingest --base HEAD --report-input-state changed",
            System.Text.Encoding.UTF8.GetString(changed.StandardOutput),
            StringComparison.Ordinal);

        File.WriteAllText(Path.Combine(fixture.Path, "D5", "Probe.lean"), leanSource);
        File.AppendAllText(Path.Combine(fixture.Path, "README.md"), "markdown-only delta\n");
        var unchanged = RunWrapper();
        Assert.Equal(0, unchanged.ExitCode);
        Assert.Contains(
            "ingest --base HEAD --report-input-state unchanged",
            System.Text.Encoding.UTF8.GetString(unchanged.StandardOutput),
            StringComparison.Ordinal);
    }
}
