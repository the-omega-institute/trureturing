using StrataLint.EngineeringScope;
using static StrataLint.TestSupport.TestExecutable;

namespace StrataLint.LeanCacheScript.Tests;

[Collection("Lean cache environment")]
public sealed class LeanCacheRunScriptTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SharedInspectorProgramsUseTheDownstreamWorkspaceOnce(bool failBuild)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TemporaryDirectory();
        var repository = Path.Combine(fixture.Path, "repository");
        var script = Path.Combine(repository, "tools/scripts/worktree/lean-cache-run.sh");
        var bin = Path.Combine(fixture.Path, "bin");
        var calls = Path.Combine(fixture.Path, "calls");
        Directory.CreateDirectory(Path.GetDirectoryName(script)!);
        Directory.CreateDirectory(bin);
        const string gitReader = "tools/scripts/worktree/lean-git/git";
        var gitTarget = Path.Combine(repository, gitReader);
        Directory.CreateDirectory(Path.GetDirectoryName(gitTarget)!);
        File.Copy(Path.Combine(TestRepositoryLayout.FindRoot(), gitReader), gitTarget);
        File.SetUnixFileMode(gitTarget, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        File.Copy(Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree/lean-cache-run.sh"), script);
        WriteExecutable(Path.Combine(bin, "dotnet"),
            "#!/bin/bash\nprintf '%s\\n' call \"$@\" >> \"$CALLS\"\nexit \"$BUILD_EXIT\"\n");
        var result = TestProcessRunner.Run("/bin/bash",
            ["-c", "PATH=\"$1:$PATH\" CALLS=\"$2\" BUILD_EXIT=\"$3\" LEAN_SKIP_LOCK=1 exec bash \"$4\" --build leanInspector/reportInspector regInspector/compiledJudgeTests regInspector/auricFibAnalysis",
                "shared-programs", bin, calls, failBuild ? "97" : "0", script],
            fixture.Path, TestBudgets.ScriptProcessHangGuard, 64 * 1024);
        Assert.Equal(failBuild ? 97 : 0, result.ExitCode);
        var arguments = File.ReadAllLines(calls);
        Assert.Single(arguments, value => value == "call");
        Assert.Contains(Path.Combine(LeanCacheGuard.PhysicalPath(repository), "tools/lean-inspector-reg"), arguments);
        Assert.Contains("--log-level=error", arguments);
        Assert.DoesNotContain(arguments, value => value.StartsWith("--fail-level", StringComparison.Ordinal));
        Assert.Contains("leanInspector/reportInspector", arguments);
        Assert.Contains("regInspector/compiledJudgeTests", arguments);
        Assert.Contains("regInspector/auricFibAnalysis", arguments);
    }

    [Fact]
    public void AdapterDelegatesWrappedCommandToCanonicalWriterJudgeWithoutExecutingItDirectly()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new TemporaryDirectory();
        var repository = Path.Combine(fixture.Path, "repository");
        var script = Path.Combine(
            repository,
            "tools",
            "scripts",
            "worktree",
            "lean-cache-run.sh");
        var bin = Path.Combine(fixture.Path, "bin");
        var arguments = Path.Combine(fixture.Path, "dotnet-arguments");
        var wrappedMarker = Path.Combine(fixture.Path, "wrapped-command-ran");
        var wrapped = Path.Combine(fixture.Path, "wrapped-command");
        Directory.CreateDirectory(Path.GetDirectoryName(script)!);
        Directory.CreateDirectory(bin);
        const string gitReader = "tools/scripts/worktree/lean-git/git";
        var gitTarget = Path.Combine(repository, gitReader);
        Directory.CreateDirectory(Path.GetDirectoryName(gitTarget)!);
        File.Copy(Path.Combine(TestRepositoryLayout.FindRoot(), gitReader), gitTarget);
        File.SetUnixFileMode(gitTarget, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        File.Copy(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree/lean-cache-run.sh"),
            script);
        WriteExecutable(
            Path.Combine(bin, "dotnet"),
            "#!/usr/bin/env bash\nprintf '%s\\n' \"$@\" > \"$DOTNET_ARGUMENTS\"\nexit 97\n");
        WriteExecutable(
            wrapped,
            "#!/usr/bin/env bash\ntouch \"$WRAPPED_MARKER\"\nexit 23\n");

        var result = TestProcessRunner.Run(
            "/bin/bash",
            [
                "-c",
                "PATH=\"$1:$PATH\" DOTNET_ARGUMENTS=\"$2\" WRAPPED_MARKER=\"$3\" exec /bin/bash \"$4\" \"$5\" payload",
                "lean-cache-run-test",
                bin,
                arguments,
                wrappedMarker,
                script,
                wrapped,
            ],
            fixture.Path,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);

        Assert.Equal(97, result.ExitCode);
        Assert.False(File.Exists(wrappedMarker));
        Assert.Equal(
            new[]
            {
                "run",
                "--project",
                Path.Combine(
                    LeanCacheGuard.PhysicalPath(repository),
                    "tools",
                    "StrataLint.Lean",
                    "StrataLint.Lean.csproj"),
                "--configuration",
                "Release",
                "--",
                "with-cache-reader",
                "--",
                wrapped,
                "payload",
            },
            File.ReadAllLines(arguments));
    }
}
