using StrataLint.Engine;

namespace StrataLint.ScriptTests;

public sealed partial class WorktreeInitScriptTests
{
    [Fact]
    public void ScriptPassesCanonicalCliErrorAndExitCodeThroughUnchanged()
    {
        if (OperatingSystem.IsWindows()) return;

        Assert.NotEmpty(TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("tools/scripts/worktree-init.sh")));

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

    internal static string PrepareFixture(string fixtureRoot)
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

    internal static ProcessOutput RunMake(
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
