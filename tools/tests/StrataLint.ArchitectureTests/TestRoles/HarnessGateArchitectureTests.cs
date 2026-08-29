using StrataLint.Engine;
using StrataLint.Tests;

namespace StrataLint.ArchitectureTests;

public sealed class HarnessGateArchitectureTests
{
    [Fact]
    public void HarnessGateUsesExternalJudgeWithoutRestoreOrBuild()
    {
        if (OperatingSystem.IsWindows()) return;

        _ = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create(".github/workflows/ci.yml"));

        var root = TestRepositoryLayout.FindRoot();
        using var fixture = new TemporaryDirectory();
        var candidateRoot = Path.Combine(fixture.Path, "candidate");
        var binDirectory = Path.Combine(fixture.Path, "bin");
        var report = Path.Combine(fixture.Path, "candidate-lean-report.json");
        var judge = Path.Combine(fixture.Path, "judge", "StrataLint.dll");
        var log = Path.Combine(fixture.Path, "dotnet.log");
        Directory.CreateDirectory(candidateRoot);
        Directory.CreateDirectory(binDirectory);
        Directory.CreateDirectory(Path.GetDirectoryName(judge)!);
        File.WriteAllText(report, "{}\n");
        File.WriteAllText(judge, string.Empty);
        WriteExecutable(
            Path.Combine(binDirectory, "dotnet"),
            """
            #!/usr/bin/env bash
            printf '%s\n' "$*" >> "$DOTNET_LOG"
            case "${2:-}" in
              check|filemap-conform) exit 0 ;;
            esac
            exit 91
            """);

        var result = TestProcessRunner.Run(
            "/bin/bash",
            [
                "-c",
                "PATH=\"$1:/usr/bin:/bin\" DOTNET_LOG=\"$2\" exec /bin/bash \"$3\" "
                + "--candidate \"$4\" --base base --candidate-lean-report \"$5\" --judge-dll \"$6\"",
                "external-judge",
                binDirectory,
                log,
                Path.Combine(root, ".github", "scripts", "harness-gate.sh"),
                candidateRoot,
                report,
                judge,
            ],
            candidateRoot,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);

        Assert.Equal(0, result.ExitCode);
        var invocations = File.ReadAllLines(log);
        Assert.Equal(2, invocations.Length);
        Assert.DoesNotContain(invocations, line => line.Contains(" selftest", StringComparison.Ordinal));
        Assert.Single(invocations, line => line.Contains(" check --protected-base base", StringComparison.Ordinal));
        Assert.Single(invocations, line => line.EndsWith(" filemap-conform", StringComparison.Ordinal));
        Assert.DoesNotContain(invocations, line =>
            line.StartsWith("restore ", StringComparison.Ordinal)
            || line.StartsWith("build ", StringComparison.Ordinal)
            || line.StartsWith("msbuild ", StringComparison.Ordinal));
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
