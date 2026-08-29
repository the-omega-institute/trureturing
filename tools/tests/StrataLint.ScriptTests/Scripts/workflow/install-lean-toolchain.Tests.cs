using System.Text.RegularExpressions;
using StrataLint.Engine;

namespace StrataLint.ScriptTests;

[ScriptSubject("tools/scripts/workflow/install-lean-toolchain.sh")]
public sealed class InstallLeanToolchainScriptTests
{
    [Fact]
    public void InstallerDefinesEachNetworkRetryLoopOnce()
    {
        var installer = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("tools/scripts/workflow/install-lean-toolchain.sh"));

        Assert.Single(Regex.Matches(installer, @"elan-init\.sh"));
        Assert.Single(Regex.Matches(installer, @"elan_install_with_retry\(\) \{"));
        Assert.Single(Regex.Matches(installer, @"elan_toolchain_with_retry\(\) \{"));
        Assert.DoesNotContain(
            "\"$HOME/.elan/bin/elan\" toolchain install \"$toolchain\"",
            installer,
            StringComparison.Ordinal);
    }

    [Fact]
    public void LeanToolchainInstallerHonorsAttemptsAndGithubPath()
    {
        if (OperatingSystem.IsWindows()) return;

        Assert.NotEmpty(TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("tools/scripts/workflow/install-lean-toolchain.sh")));

        var root = TestRepositoryLayout.FindRoot();
        var installer = Path.Combine(root, "tools", "scripts", "workflow", "install-lean-toolchain.sh");
        using var fixture = new TemporaryDirectory();
        var home = Path.Combine(fixture.Path, "home");
        var elanBin = Path.Combine(home, ".elan", "bin");
        var stubBin = Path.Combine(fixture.Path, "bin");
        var attempts = Path.Combine(fixture.Path, "attempts.log");
        var githubPath = Path.Combine(fixture.Path, "github-path");
        var toolchain = Path.Combine(fixture.Path, "lean-toolchain");
        Directory.CreateDirectory(elanBin);
        Directory.CreateDirectory(stubBin);
        File.WriteAllText(toolchain, "leanprover/lean4:v4.24.0\n");
        File.WriteAllText(
            Path.Combine(elanBin, "elan"),
            "#!/usr/bin/env bash\n"
                + "if [[ \"${1:-}\" == toolchain && \"${2:-}\" == list ]]; then exit 0; fi\n"
                + "if [[ \"${1:-}\" == toolchain && \"${2:-}\" == install ]]; then printf 'attempt\\n' >> \"$ATTEMPTS_LOG\"; exit 42; fi\n"
                + "exit 0\n");
        File.WriteAllText(Path.Combine(stubBin, "sleep"), "#!/usr/bin/env bash\nexit 0\n");
        File.SetUnixFileMode(
            Path.Combine(elanBin, "elan"),
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        File.SetUnixFileMode(
            Path.Combine(stubBin, "sleep"),
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);

        var result = TestProcessRunner.Run(
            "env",
            [
                $"HOME={home}",
                $"PATH={stubBin}:{Environment.GetEnvironmentVariable("PATH")}",
                $"ATTEMPTS_LOG={attempts}",
                "/bin/bash",
                installer,
                toolchain,
                "--attempts",
                "2",
                "--github-path",
                githubPath,
            ],
            root,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);

        Assert.Equal(1, result.ExitCode);
        Assert.Equal(2, File.ReadAllLines(attempts).Length);
        Assert.Equal([elanBin], File.ReadAllLines(githubPath));
    }
}
