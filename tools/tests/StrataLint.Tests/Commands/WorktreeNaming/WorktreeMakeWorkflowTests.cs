using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class WorktreeMakeWorkflowTests
{
    private const string WorktreeInitScriptPath = "tools/scripts/worktree-init.sh";

    [Fact]
    public void MakePassesRequestedBranchToCanonicalCli()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new TemporaryDirectory();
        var marker = PrepareFixture(fixture.Path);
        var target = Path.Combine(fixture.Path, "target");

        var result = RunMake(
            fixture.Path,
            marker,
            "worktree",
            "KIND=sentinel-kind",
            "NAME=w99-foo",
            $"DEST={target}",
            "BASE=HEAD");

        Assert.Equal(0, result.ExitCode);
        Assert.True(File.Exists(marker));
        Assert.False(Directory.Exists(target));
        var arguments = System.Text.Encoding.UTF8.GetString(result.StandardOutput)
            .Split('\n', StringSplitOptions.RemoveEmptyEntries);
        var branchFlag = Array.IndexOf(arguments, "--branch");
        Assert.True(branchFlag >= 0, "worktree adapter must pass --branch");
        Assert.Equal("harness/sentinel-kind/w99-foo", arguments[branchFlag + 1]);
        var pathFlag = Array.IndexOf(arguments, "--path");
        Assert.True(pathFlag >= 0, "worktree adapter must pass --path");
        Assert.Equal(target, arguments[pathFlag + 1]);
    }

    [Fact]
    public void ScriptPassesCanonicalCliErrorAndExitCodeThroughUnchanged()
    {
        if (OperatingSystem.IsWindows()) return;

        using var fixture = new TemporaryDirectory();
        var marker = PrepareFixture(fixture.Path);

        var result = RunScript(
            fixture.Path,
            marker,
            "canonical failure");

        Assert.Equal(23, result.ExitCode);
        Assert.Equal(
            "canonical failure\n",
            System.Text.Encoding.UTF8.GetString(result.StandardError));
        Assert.True(File.Exists(marker));
    }

    private static string PrepareFixture(string fixtureRoot)
    {
        if (OperatingSystem.IsWindows())
        {
            throw new PlatformNotSupportedException("worktree make fixtures require a Unix shell");
        }

        var root = TestRepositoryLayout.FindRoot();
        var scriptDirectory = Path.Combine(fixtureRoot, "tools", "scripts");
        var binDirectory = Path.Combine(fixtureRoot, "bin");
        Directory.CreateDirectory(scriptDirectory);
        Directory.CreateDirectory(binDirectory);
        File.Copy(Path.Combine(root, "Makefile"), Path.Combine(fixtureRoot, "Makefile"));
        File.Copy(
            Path.Combine(root, WorktreeInitScriptPath),
            Path.Combine(fixtureRoot, WorktreeInitScriptPath));
        var dotnet = Path.Combine(binDirectory, "dotnet");
        File.WriteAllText(
            dotnet,
            "#!/usr/bin/env bash\nprintf 'called\\n' > \"$DOTNET_MARKER\"\nprintf '%s\\n' \"$@\"\nif [[ -n \"${DOTNET_STDERR:-}\" ]]; then printf '%s\\n' \"$DOTNET_STDERR\" >&2; fi\nexit \"${DOTNET_EXIT:-0}\"\n");
        File.SetUnixFileMode(
            dotnet,
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        ReviewRegressionTests.RunGit(fixtureRoot, "init", "--initial-branch=dev");
        return Path.Combine(fixtureRoot, "dotnet-called");
    }

    private static ProcessOutput RunMake(
        string fixtureRoot,
        string marker,
        params string[] arguments)
    {
        var binDirectory = Path.Combine(fixtureRoot, "bin");
        var commandArguments = new List<string>
        {
            "-c",
            "export PATH=\"$1:/usr/bin:/bin\"; export DOTNET_MARKER=\"$2\"; shift 2; exec make --no-print-directory \"$@\"",
            "worktree-make",
            binDirectory,
            marker,
        };
        commandArguments.AddRange(arguments);
        return TestProcessRunner.Run(
            "/bin/bash",
            commandArguments,
            fixtureRoot,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);
    }

    private static ProcessOutput RunScript(
        string fixtureRoot,
        string marker,
        string error)
    {
        var binDirectory = Path.Combine(fixtureRoot, "bin");
        return TestProcessRunner.Run(
            "/bin/bash",
            [
                "-c",
                "export PATH=\"$1:/usr/bin:/bin\"; export DOTNET_MARKER=\"$2\"; export DOTNET_EXIT=23; export DOTNET_STDERR=\"$3\"; exec /bin/bash tools/scripts/worktree-init.sh missing task target HEAD",
                "worktree-script",
                binDirectory,
                marker,
                error,
            ],
            fixtureRoot,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);
    }
}
