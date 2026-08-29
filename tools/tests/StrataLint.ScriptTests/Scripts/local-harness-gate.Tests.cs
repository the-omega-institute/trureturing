using System.Text;
using StrataLint.Engine;

namespace StrataLint.ScriptTests;

[ScriptSubject("tools/scripts/local-harness-gate.sh")]
public sealed partial class LocalHarnessGateScriptTests
{
    private const string LocalHarnessGateScriptPath = "tools/scripts/local-harness-gate.sh";
    private const string GateForkSha = "0000000000000000000000000000000000000001";
    private const string GateBaseTipSha = "0000000000000000000000000000000000000004";
    private const string GateAdvancedBaseTipSha = "0000000000000000000000000000000000000005";

    [Fact]
    public void LocalGateHonorsExplicitTemporaryDirectory()
    {
        var localGate = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("tools/scripts/local-harness-gate.sh"));

        Assert.Contains(
            "mktemp -d \"${TMPDIR:-/tmp}/stratalint-local-gate.XXXXXXXX\"",
            localGate,
            StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("candidate-failed")]
    [InlineData("command-failed")]
    [InlineData("empty")]
    [InlineData("zero")]
    [InlineData("vacuous")]
    public void LocalHarnessGateRejectsInvalidMergeBase(string mergeBaseMode)
    {
        if (OperatingSystem.IsWindows()) return;

        AssertLocalHarnessGateSubjectExists();

        var result = PreflightScriptTests.RunInvalidMergeBase(LocalHarnessGateScriptPath, mergeBaseMode);
        var error = Encoding.UTF8.GetString(result.StandardError);

        Assert.True(
            result.ExitCode == 1,
            $"expected exit 1, actual {result.ExitCode}\nstdout:\n{Encoding.UTF8.GetString(result.StandardOutput)}\nstderr:\n{error}");
        Assert.Contains(PreflightScriptTests.ExpectedMergeBaseDiagnostic(mergeBaseMode), error, StringComparison.Ordinal);
        if (mergeBaseMode == "candidate-failed")
        {
            Assert.DoesNotContain("BASE_ADVANCED", error, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void LocalHarnessGateBaseResolutionFailureDiagnosticsCarryResolvedAndEmptyValues()
    {
        if (OperatingSystem.IsWindows()) return;

        AssertLocalHarnessGateSubjectExists();

        var result = PreflightScriptTests.RunInvalidMergeBase(LocalHarnessGateScriptPath, "base-ref-failed");
        var error = Encoding.UTF8.GetString(result.StandardError);

        Assert.Equal(1, result.ExitCode);
        Assert.Contains(
            PreflightScriptTests.ExpectedMergeBaseDiagnostic("base-ref-failed"),
            error,
            StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(GateBaseTipSha, false)]
    [InlineData("base", true)]
    public void LocalHarnessGateResolvesSymbolicAndFullOidBaseTipsToFork(
        string baseArgument,
        bool expectAdvanceAdvisory)
    {
        if (OperatingSystem.IsWindows()) return;

        AssertLocalHarnessGateSubjectExists();

        var root = TestRepositoryLayout.FindRoot();
        using var fixture = new TemporaryDirectory();
        var candidateRoot = Path.Combine(fixture.Path, "candidate");
        var homeDirectory = Path.Combine(fixture.Path, "home");
        var binDirectory = Path.Combine(homeDirectory, ".dotnet");
        var candidateDll = Path.Combine(candidateRoot, "bin", "candidate.dll");
        var baseRefCount = Path.Combine(fixture.Path, "base-ref-count");
        Directory.CreateDirectory(Path.GetDirectoryName(candidateDll)!);
        Directory.CreateDirectory(binDirectory);
        File.WriteAllText(candidateDll, string.Empty);
        PreflightScriptTests.WriteHarnessGateChainReportPair(candidateRoot);
        PreflightScriptTests.WriteHarnessGateChainDotnetShim(binDirectory);
        WriteExecutable(Path.Combine(binDirectory, "lake"), "#!/usr/bin/env bash\nexit 0");
        PreflightScriptTests.WriteObservedBaseGitShim(binDirectory, candidateRoot, baseArgument);

        var result = TestProcessRunner.Run(
            "/bin/bash",
            [
                "-c",
                "HOME=\"$1\" PATH=\"$2:/usr/bin:/bin\" PREFLIGHT_ADMISSION_RC=0 "
                    + "PREFLIGHT_EXPECTED_GATE_BASE=\"$3\" GATE_BASE_REF_COUNT=\"$4\" "
                    + "exec /bin/bash \"$5\" --candidate \"$6\" --base \"$7\" --skip-engineering",
                "local-gate-base-resolution",
                homeDirectory,
                binDirectory,
                GateForkSha,
                baseRefCount,
                Path.Combine(root, LocalHarnessGateScriptPath),
                candidateRoot,
                baseArgument,
            ],
            candidateRoot,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);

        var error = Encoding.UTF8.GetString(result.StandardError);
        Assert.True(
            result.ExitCode == 0,
            $"expected exit 0, actual {result.ExitCode}\nstdout:\n{Encoding.UTF8.GetString(result.StandardOutput)}\nstderr:\n{error}");
        Assert.Contains($"base={GateForkSha}", error, StringComparison.Ordinal);
        if (expectAdvanceAdvisory)
        {
            Assert.Contains(
                $"BASE_ADVANCED pinned={GateBaseTipSha} observed={GateAdvancedBaseTipSha}",
                error,
                StringComparison.Ordinal);
        }
        else
        {
            Assert.DoesNotContain("BASE_ADVANCED", error, StringComparison.Ordinal);
        }
    }


    private static void AssertLocalHarnessGateSubjectExists() =>
        Assert.NotEmpty(TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("tools/scripts/local-harness-gate.sh")));

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static void WriteExecutable(string path, string content)
    {
        File.WriteAllText(path, content + "\n");
        File.SetUnixFileMode(
            path,
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
    }
}
