using StrataLint.Engine;
using StrataLint.Cli;

namespace StrataLint.ScriptTests;

[ScriptSubject("tools/scripts/worktree/lean-cache-run.sh")]
[Collection("Lean cache environment")]
public sealed class LeanCacheRunScriptTests
{
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
        File.Copy(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree/lean-cache-run.sh"),
            script);
        WriteExecutable(
            Path.Combine(bin, "dotnet"),
            "#!/usr/bin/env bash\nprintf '%s\\n' \"$@\" > \"$DOTNET_ARGUMENTS\"\nexit 97");
        WriteExecutable(
            wrapped,
            "#!/usr/bin/env bash\ntouch \"$WRAPPED_MARKER\"\nexit 23");

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
                    "StrataLint.Cli",
                    "StrataLint.Cli.csproj"),
                "--configuration",
                "Release",
                "--",
                "worktree",
                "with-cache-writer",
                "--",
                wrapped,
                "payload",
            },
            File.ReadAllLines(arguments));
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static void WriteExecutable(string path, string content)
    {
        File.WriteAllText(path, content + "\n");
        File.SetUnixFileMode(
            path,
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
    }
}
