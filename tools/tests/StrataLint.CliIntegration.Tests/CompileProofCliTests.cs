using System.Text;
using StrataLint.Cli;

namespace StrataLint.CliIntegration.Tests;

public sealed class CompileProofCliTests
{
    [Theory]
    [InlineData("capability-proof", "matched", 0)]
    [InlineData("banned-api-proof", "matched", 0)]
    [InlineData("capability-proof", "successful-build", 1)]
    [InlineData("banned-api-proof", "successful-build", 1)]
    [InlineData("capability-proof", "wrong-diagnostic", 1)]
    [InlineData("banned-api-proof", "wrong-line", 1)]
    [InlineData("banned-api-proof", "extra-error", 1)]
    [InlineData("capability-proof", "restore-failed", 2)]
    [InlineData("banned-api-proof", "restore-failed", 2)]
    [InlineData("capability-proof", "infrastructure", 2)]
    [InlineData("banned-api-proof", "missing-source", 2)]
    [InlineData("unknown", "matched", 2)]
    public void CompileProofRunsWithoutStagesAndRequiresTheExpectedRejection(string proof, string scenario, int expectedExit)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new TemporaryDirectory();
        var bin = Path.Combine(fixture.Path, "bin");
        Directory.CreateDirectory(bin);
        var log = Path.Combine(fixture.Path, "commands");
        var source = Path.Combine(fixture.Path, "tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs");
        Directory.CreateDirectory(Path.GetDirectoryName(source)!);
        if (scenario != "missing-source") File.WriteAllText(source, "// header\n// banned-api-proof\n");
        var shim = Path.Combine(bin, "dotnet");
        File.WriteAllText(shim, """
            #!/bin/bash
            set -euo pipefail
            printf '%s\n' "$*" >> "$PROOF_LOG"
            if [[ "$1" == restore ]]; then
              [[ "$PROOF_SCENARIO" != restore-failed ]] || exit 1
              exit 0
            fi
            [[ "$1" == build ]] || exit 127
            [[ "$PROOF_SCENARIO" != infrastructure ]] || exit 127
            [[ "$PROOF_SCENARIO" != successful-build ]] || exit 0
            if [[ "$PROOF_KIND" == capability-proof ]]; then
              if [[ "$PROOF_SCENARIO" == wrong-diagnostic ]]; then
                printf 'MissingCapability.cs(13,9): error CS1000: invalid\n'
              else
                printf 'MissingCapability.cs(13,9): error CS7036: missing metaClear\n'
              fi
            else
              line=2
              [[ "$PROOF_SCENARIO" != wrong-line ]] || line=3
              printf 'BannedApiViolations.cs(%s,1): error RS0030: banned symbol\n' "$line"
              [[ "$PROOF_SCENARIO" != extra-error ]] || printf 'Other.cs(1,1): error CS1000: invalid\n'
            fi
            exit 1
            """);
        File.SetUnixFileMode(shim, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var result = TestProcessRunner.Run("env", ["PATH=" + bin + ":/usr/bin:/bin", "PROOF_LOG=" + log,
            "PROOF_KIND=" + proof, "PROOF_SCENARIO=" + scenario, Path.Combine(Path.GetDirectoryName(typeof(Program).Assembly.Location)!, "StrataLint"),
            "compile-proof", proof], fixture.Path, TestBudgets.ScriptProcessHangGuard, 64 * 1024);
        var output = Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError);
        Assert.True(result.ExitCode == expectedExit, $"expected {expectedExit}, actual {result.ExitCode}: {output}");
        Assert.False(Directory.Exists(Path.Combine(fixture.Path, "build/ci")));
        if (expectedExit == 0)
        {
            Assert.Contains("EXPECTED_DIAGNOSTIC", output, StringComparison.Ordinal);
            Assert.Contains("\"status\":\"matched\"", output, StringComparison.Ordinal);
            var commands = File.ReadAllLines(log);
            Assert.Equal(2, commands.Length);
            Assert.StartsWith("restore ", commands[0], StringComparison.Ordinal);
            Assert.Contains("--locked-mode -nr:false", commands[0], StringComparison.Ordinal);
            Assert.StartsWith("build ", commands[1], StringComparison.Ordinal);
            Assert.Contains("--no-restore --no-dependencies --configuration Release -nr:false", commands[1], StringComparison.Ordinal);
        }
        else Assert.DoesNotContain("EXPECTED_DIAGNOSTIC", output, StringComparison.Ordinal);
    }
}
