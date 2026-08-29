using System.Text.RegularExpressions;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.ScriptTests;

public sealed partial class RootMakefileTests
{
    [Fact]
    public void EchoResidualSummaryRunsMakeAndKeepsDiagnosticsOutOfThePasteableBlock()
    {
        if (OperatingSystem.IsWindows()) return;

        var root = TestRepositoryLayout.FindRoot();
        using var fixture = new TemporaryDirectory();
        var reportDirectory = Path.Combine(fixture.Path, "tools", "scripts", "report");
        var cliDirectory = Path.Combine(fixture.Path, "tools", "StrataLint.Cli");
        var binDirectory = Path.Combine(fixture.Path, "bin");
        Directory.CreateDirectory(reportDirectory);
        Directory.CreateDirectory(cliDirectory);
        Directory.CreateDirectory(binDirectory);
        File.Copy(Path.Combine(root, "Makefile"), Path.Combine(fixture.Path, "Makefile"));
        File.Copy(
            Path.Combine(root, EchoResidualSummaryScriptPath),
            Path.Combine(fixture.Path, EchoResidualSummaryScriptPath));
        File.WriteAllText(
            Path.Combine(fixture.Path, LeanReportScriptPath),
            "#!/usr/bin/env bash\nprintf 'lean provenance\\n' >&2\n");
        File.WriteAllText(
            Path.Combine(binDirectory, "dotnet"),
            """
            #!/usr/bin/env bash
            [[ "$*" == *"echo-verify --emit --base synthetic-base"* ]] || exit 19
            printf '%s\n' '<!-- echo-residual-summary:v3 residual=sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa -->' '# Echo Residual Summary'
            """);
        File.SetUnixFileMode(
            Path.Combine(fixture.Path, LeanReportScriptPath),
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        File.SetUnixFileMode(
            Path.Combine(binDirectory, "dotnet"),
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);

        var result = TestProcessRunner.Run(
            "/bin/bash",
            ["-c", "PATH=\"$1:$PATH\" exec make --no-print-directory echo-residual-summary BASE=synthetic-base", "echo-make", binDirectory],
            fixture.Path,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(
            """
            <!-- echo-residual-summary:v3 residual=sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa -->
            # Echo Residual Summary
            """ + "\n",
            System.Text.Encoding.UTF8.GetString(result.StandardOutput));
        Assert.Equal("lean provenance\n", System.Text.Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void TheoryCandidatesOwnerOverrideFilePreservesBytesAcrossMakeBoundary()
    {
        if (OperatingSystem.IsWindows()) return;

        var root = TestRepositoryLayout.FindRoot();
        using var fixture = new TemporaryDirectory();
        var binDirectory = Path.Combine(fixture.Path, "bin");
        var cliDirectory = Path.Combine(fixture.Path, "tools", "StrataLint.Cli");
        Directory.CreateDirectory(binDirectory);
        Directory.CreateDirectory(cliDirectory);
        File.Copy(Path.Combine(root, "Makefile"), Path.Combine(fixture.Path, "Makefile"));
        var problemBytes = System.Text.Encoding.UTF8.GetBytes(
            "Does \"x\" imply $HOME and `id`?\nClassify ξ exactly.\n");
        var problemPath = Path.Combine(fixture.Path, "owner-problem.txt");
        File.WriteAllBytes(problemPath, problemBytes);
        var dotnetPath = Path.Combine(binDirectory, "dotnet");
        File.WriteAllText(
            dotnetPath,
            """
            #!/usr/bin/env bash
            while [[ $# -gt 0 ]]; do
              if [[ "$1" == "--owner-override-file" && $# -ge 2 ]]; then
                /bin/cat -- "$2"
                exit 0
              fi
              shift
            done
            exit 21
            """ + "\n");
        File.SetUnixFileMode(
            dotnetPath,
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);

        var result = TestProcessRunner.Run(
            "/bin/bash",
            [
                "-c",
                "PATH=\"$1:$PATH\" exec make --no-print-directory theory-candidates OWNER_OVERRIDE_FILE=\"$2\"",
                "theory-candidates-make",
                binDirectory,
                problemPath,
            ],
            fixture.Path,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(problemBytes, result.StandardOutput);
        Assert.Empty(result.StandardError);
    }

    [Fact]
    public void MakePassesStructuredCreationInputsToCanonicalCli()
    {
        if (OperatingSystem.IsWindows()) return;

        Assert.NotEmpty(TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("Makefile")));

        using var fixture = new TemporaryDirectory();
        var marker = WorktreeInitScriptTests.PrepareFixture(fixture.Path);
        var target = Path.Combine(fixture.Path, "target");

        var result = WorktreeInitScriptTests.RunMake(
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
        var kindFlag = Array.IndexOf(arguments, "--kind");
        Assert.True(kindFlag >= 0, "worktree adapter must pass --kind");
        Assert.Equal("sentinel-kind", arguments[kindFlag + 1]);
        var nameFlag = Array.IndexOf(arguments, "--name");
        Assert.True(nameFlag >= 0, "worktree adapter must pass --name");
        Assert.Equal("w99-foo", arguments[nameFlag + 1]);
        Assert.DoesNotContain("--branch", arguments);
        var pathFlag = Array.IndexOf(arguments, "--path");
        Assert.True(pathFlag >= 0, "worktree adapter must pass --path");
        Assert.Equal(target, arguments[pathFlag + 1]);
    }
}
