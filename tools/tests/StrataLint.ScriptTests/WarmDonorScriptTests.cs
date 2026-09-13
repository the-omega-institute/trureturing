using System.Text;

namespace StrataLint.Tests;

public sealed class WarmDonorScriptTests
{
    // The shell entrypoint delegates to the CLI. SharedLakeCacheTests and
    // NativeSharedLakeCacheTests cover selected-checkout warming and writer ownership.
    [Theory]
    [InlineData(0)]
    [InlineData(42)]
    public void WarmDonorDelegatesToCanonicalCliAndPreservesItsResult(int cliExit)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TemporaryDirectory();
        var repository = Path.Combine(fixture.Path, "repository");
        var script = Path.Combine(repository, "tools/scripts/worktree/warm-donor.sh");
        var bin = Path.Combine(fixture.Path, "bin");
        var calls = Path.Combine(fixture.Path, "calls");
        ScriptHarnessScratch.EnsureDirectory(bin);
        ScriptHarnessScratch.CopyScriptInto(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree/warm-donor.sh"), script);
        WriteExecutable(Path.Combine(bin, "dotnet"), """
            printf '%s\n' "$PWD" "$@" > "$WARM_CALLS"
            printf 'cli stdout\n'
            printf 'cli stderr\n' >&2
            exit "$WARM_CLI_EXIT"
            """);
        foreach (var tool in new[] { "git", "make" })
            WriteExecutable(Path.Combine(bin, tool), "echo 'unexpected legacy warming command' >&2; exit 97");

        var result = TestProcessRunner.Run("/usr/bin/env",
            [
                $"PATH={bin}:{Environment.GetEnvironmentVariable("PATH")}",
                $"WARM_CALLS={calls}",
                $"WARM_CLI_EXIT={cliExit.ToString(System.Globalization.CultureInfo.InvariantCulture)}",
                "/bin/bash", script,
            ], fixture.Path, TestBudgets.ScriptProcessHangGuard, 64 * 1024);

        Assert.Equal(cliExit, result.ExitCode);
        Assert.Equal("cli stdout\n", Encoding.UTF8.GetString(result.StandardOutput));
        Assert.Equal("cli stderr\n", Encoding.UTF8.GetString(result.StandardError));
        Assert.Equal(
            [
                repository, "run", "--project",
                Path.Combine(repository, "tools/StrataLint.Cli/StrataLint.Cli.csproj"),
                "--configuration", "Release", "--", "worktree", "warm-cache",
            ], ScriptHarnessScratch.ReadScratchLines(calls));
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static void WriteExecutable(string path, string body)
    {
        ScriptHarnessScratch.WriteScratchText(path, "#!/usr/bin/env bash\nset -euo pipefail\n" + body + "\n");
        File.SetUnixFileMode(path,
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
    }
}
