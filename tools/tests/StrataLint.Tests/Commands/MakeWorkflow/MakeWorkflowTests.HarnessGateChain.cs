using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class MakeWorkflowTests
{
    private const string GateForkSha = "0000000000000000000000000000000000000001";
    private const string GateCandidateSha = "0000000000000000000000000000000000000002";
    private const string GateBaseTipSha = "0000000000000000000000000000000000000004";
    private const string GateAdvancedBaseTipSha = "0000000000000000000000000000000000000005";

    [Fact]
    public void ScribeContentChecksUseTheExplicitNonEmptyReport()
    {
        if (OperatingSystem.IsWindows()) return;

        var root = TestRepositoryLayout.FindRoot();
        using var fixture = new TemporaryDirectory();
        var binDirectory = Path.Combine(fixture.Path, "bin");
        var explicitReport = Path.Combine(fixture.Path, "explicit-report.json");
        var ambientReport = Path.Combine(fixture.Path, "ambient-report.json");
        var scribe = Path.Combine(fixture.Path, "StrataLint.Scribe.dll");
        var log = Path.Combine(fixture.Path, "scribe.log");
        Directory.CreateDirectory(binDirectory);
        File.WriteAllText(explicitReport, "explicit\n");
        File.WriteAllText(ambientReport, "ambient\n");
        File.WriteAllText(scribe, "fixture\n");
        WriteExecutable(
            Path.Combine(binDirectory, "dotnet"),
            "#!/usr/bin/env bash\nprintf '%s|%s\\n' \"$STRATALINT_LEAN_REPORT\" \"$*\" >> \"$SCRIBE_LOG\"");
        var headResult = TestProcessRunner.Run(
            "git",
            ["rev-parse", "HEAD"],
            root,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);
        Assert.Equal(0, headResult.ExitCode);
        var baseRevision = Encoding.UTF8.GetString(headResult.StandardOutput).Trim();
        WriteExecutable(
            Path.Combine(binDirectory, "git"),
            $$"""
            #!/usr/bin/env bash
            if [[ "${1:-}" == -C ]]; then shift 2; fi
            case "$*" in
              "cat-file -e {{baseRevision}}^{commit}"|"ls-files --others --exclude-standard -z") exit 0 ;;
              "diff --name-only --no-renames -z {{baseRevision}} --") printf 'Blueprint/D5/Probe.scribe.cs\0' ;;
              *) echo "unexpected git invocation: $*" >&2; exit 90 ;;
            esac
            """);

        var result = TestProcessRunner.Run(
            "/bin/bash",
            [
                "-c",
                "PATH=\"$1:/usr/bin:/bin\" STRATALINT_LEAN_REPORT=\"$2\" SCRIBE_LOG=\"$3\" "
                    + "exec /bin/bash \"$4\" \"$5\" \"$6\" \"$7\"",
                "scribe-content-checks",
                binDirectory,
                ambientReport,
                log,
                Path.Combine(root, ScribeContentChecksScriptPath),
                explicitReport,
                scribe,
                baseRevision,
            ],
            root,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);

        Assert.True(
            result.ExitCode == 0,
            $"expected exit 0, actual {result.ExitCode}\nstdout:\n{Encoding.UTF8.GetString(result.StandardOutput)}\nstderr:\n{Encoding.UTF8.GetString(result.StandardError)}");
        var invocations = File.ReadAllLines(log);
        Assert.Equal(2, invocations.Length);
        Assert.All(invocations, line => Assert.StartsWith(explicitReport + "|", line, StringComparison.Ordinal));
        Assert.DoesNotContain(invocations, line => line.Contains(ambientReport, StringComparison.Ordinal));
        Assert.Contains(
            invocations,
            static line => line.EndsWith(" describe-report --check", StringComparison.Ordinal));
        Assert.Contains(
            invocations,
            line => line.EndsWith(
                $" markdown-check --report {explicitReport} --paths-from -",
                StringComparison.Ordinal));
    }

    [Fact]
    public void ScribeContentChecksRejectMissingAndEmptyReportsBeforeRunningScribe()
    {
        if (OperatingSystem.IsWindows()) return;

        var root = TestRepositoryLayout.FindRoot();
        using var fixture = new TemporaryDirectory();
        var binDirectory = Path.Combine(fixture.Path, "bin");
        var emptyReport = Path.Combine(fixture.Path, "empty-report.json");
        var missingReport = Path.Combine(fixture.Path, "missing-report.json");
        var scribe = Path.Combine(fixture.Path, "StrataLint.Scribe.dll");
        Directory.CreateDirectory(binDirectory);
        File.WriteAllText(emptyReport, string.Empty);
        File.WriteAllText(scribe, "fixture\n");
        WriteExecutable(Path.Combine(binDirectory, "dotnet"), "#!/usr/bin/env bash\nexit 0");

        foreach (var report in new[] { emptyReport, missingReport })
        {
            var result = TestProcessRunner.Run(
                "/bin/bash",
                [
                    "-c",
                    "PATH=\"$1:/usr/bin:/bin\" exec /bin/bash \"$2\" \"$3\" \"$4\"",
                    "scribe-content-checks-invalid-report",
                    binDirectory,
                    Path.Combine(root, ScribeContentChecksScriptPath),
                    report,
                    scribe,
                ],
                root,
                BoundedProcessRunner.HangDetectionBudget,
                64 * 1024);

            Assert.NotEqual(0, result.ExitCode);
        }
    }

    [Fact]
    public void HarnessGateUsesExternalJudgeWithoutRestoreOrBuild()
    {
        if (OperatingSystem.IsWindows()) return;

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

    [Theory]
    [InlineData(1, 1)]
    [InlineData(2, 2)]
    [InlineData(3, 0)]
    public void PreflightPreservesHarnessGateExitCodeAcrossTheFullChain(
        int admissionExitCode,
        int expectedExitCode)
    {
        if (OperatingSystem.IsWindows()) return;

        var root = TestRepositoryLayout.FindRoot();
        using var fixture = new TemporaryDirectory();
        var candidateRoot = Path.Combine(fixture.Path, "candidate");
        var homeDirectory = Path.Combine(fixture.Path, "home");
        var binDirectory = Path.Combine(homeDirectory, ".dotnet");
        var candidateDll = Path.Combine(candidateRoot, "bin", "candidate.dll");
        Directory.CreateDirectory(Path.GetDirectoryName(candidateDll)!);
        Directory.CreateDirectory(binDirectory);
        File.WriteAllText(candidateDll, string.Empty);
        WriteHarnessGateChainReportPair(candidateRoot);

        WriteHarnessGateChainGitShim(binDirectory, candidateRoot);
        WriteHarnessGateChainDotnetShim(binDirectory);
        WriteExecutable(
            Path.Combine(binDirectory, "lake"),
            "#!/usr/bin/env bash\n[[ \"${1:-}\" == --version ]] || exit 64\nexit 0");
        WriteHarnessGateChainMakeShim(binDirectory);

        var result = TestProcessRunner.Run(
            "/bin/bash",
            [
                "-c",
                "PREFLIGHT_ADMISSION_RC=\"$1\" PREFLIGHT_CANDIDATE_ROOT=\"$2\" "
                + "PREFLIGHT_GATE=\"$3\" PREFLIGHT_LOCAL_GATE=\"$4\" "
                + "HOME=\"$5\" BASE=base PATH=\"$6:/usr/bin:/bin\" "
                + "exec /bin/bash \"$7\"",
                "preflight-harness-gate-chain",
                admissionExitCode.ToString(System.Globalization.CultureInfo.InvariantCulture),
                candidateRoot,
                Path.Combine(root, ".github", "scripts", "harness-gate.sh"),
                Path.Combine(root, LocalHarnessGateScriptPath),
                homeDirectory,
                binDirectory,
                Path.Combine(root, PreflightScriptPath),
            ],
            candidateRoot,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);

        var output = Encoding.UTF8.GetString(result.StandardOutput);
        var error = Encoding.UTF8.GetString(result.StandardError);
        Assert.True(
            expectedExitCode == result.ExitCode,
            $"expected exit {expectedExitCode}, actual {result.ExitCode}\nstdout:\n{output}\nstderr:\n{error}");
    }

    [Theory]
    [InlineData(1, 1, true)]
    [InlineData(2, 2, true)]
    [InlineData(3, 0, false)]
    public void PreflightUsesForkPointWhenBaseTipHasAdvancedWithoutMutatingGit(
        int admissionExitCode,
        int expectedExitCode,
        bool diverged)
    {
        if (OperatingSystem.IsWindows()) return;

        var root = TestRepositoryLayout.FindRoot();
        using var fixture = new TemporaryDirectory();
        var candidateRoot = Path.Combine(fixture.Path, "candidate");
        var homeDirectory = Path.Combine(fixture.Path, "home");
        var binDirectory = Path.Combine(homeDirectory, ".dotnet");
        var candidateDll = Path.Combine(candidateRoot, "bin", "candidate.dll");
        var gitState = Path.Combine(fixture.Path, "git-state");
        var baseTipSha = diverged ? GateBaseTipSha : GateForkSha;
        Directory.CreateDirectory(Path.GetDirectoryName(candidateDll)!);
        Directory.CreateDirectory(binDirectory);
        File.WriteAllText(candidateDll, string.Empty);
        var gitStateBefore = Encoding.UTF8.GetBytes(diverged
            ? $"HEAD {GateCandidateSha} {GateForkSha}\nBASE {baseTipSha} 0000000000000000000000000000000000000003 {GateForkSha}\nrefs {GateCandidateSha} {baseTipSha}\n"
            : $"HEAD {GateCandidateSha} {baseTipSha}\nrefs {GateCandidateSha} {baseTipSha}\n");
        File.WriteAllBytes(gitState, gitStateBefore);
        WriteHarnessGateChainReportPair(candidateRoot);

        WriteHarnessGateChainForkPointGitShim(
            binDirectory,
            candidateRoot,
            baseTipSha,
            GateCandidateSha,
            GateForkSha,
            diverged);
        WriteHarnessGateChainDotnetShim(binDirectory);
        WriteExecutable(
            Path.Combine(binDirectory, "lake"),
            "#!/usr/bin/env bash\n[[ \"${1:-}\" == --version ]] || exit 64\nexit 0");
        WriteHarnessGateChainMakeShim(binDirectory);

        var result = TestProcessRunner.Run(
            "/bin/bash",
            [
                "-c",
                "PREFLIGHT_ADMISSION_RC=\"$1\" PREFLIGHT_CANDIDATE_ROOT=\"$2\" "
                + "PREFLIGHT_GATE=\"$3\" PREFLIGHT_LOCAL_GATE=\"$4\" "
                + "HOME=\"$5\" BASE=base PATH=\"$6:/usr/bin:/bin\" "
                + "PREFLIGHT_GIT_STATE=\"$7\" PREFLIGHT_EXPECTED_GATE_BASE=\"$8\" exec /bin/bash \"$9\"",
                "preflight-fork-point",
                admissionExitCode.ToString(System.Globalization.CultureInfo.InvariantCulture),
                candidateRoot,
                Path.Combine(root, ".github", "scripts", "harness-gate.sh"),
                Path.Combine(root, LocalHarnessGateScriptPath),
                homeDirectory,
                binDirectory,
                gitState,
                GateForkSha,
                Path.Combine(root, PreflightScriptPath),
            ],
            candidateRoot,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);

        var output = Encoding.UTF8.GetString(result.StandardOutput);
        Assert.True(
            expectedExitCode == result.ExitCode,
            $"expected exit {expectedExitCode}, actual {result.ExitCode}\nstdout:\n{output}\nstderr:\n{Encoding.UTF8.GetString(result.StandardError)}");
        Assert.Contains("[preflight] dotnet", output, StringComparison.Ordinal);
        Assert.Equal(gitStateBefore, File.ReadAllBytes(gitState));
    }

    [Theory]
    [InlineData("candidate-failed")]
    [InlineData("command-failed")]
    [InlineData("empty")]
    [InlineData("zero")]
    [InlineData("vacuous")]
    public void PreflightRejectsInvalidMergeBaseBeforeExpensiveStages(string mergeBaseMode)
    {
        if (OperatingSystem.IsWindows()) return;

        var result = RunInvalidMergeBase(PreflightScriptPath, mergeBaseMode);
        var output = Encoding.UTF8.GetString(result.StandardOutput);
        var error = Encoding.UTF8.GetString(result.StandardError);

        Assert.Equal(1, result.ExitCode);
        Assert.DoesNotContain("[preflight] dotnet", output, StringComparison.Ordinal);
        Assert.Contains(ExpectedMergeBaseDiagnostic(mergeBaseMode), error, StringComparison.Ordinal);
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

        var result = RunInvalidMergeBase(LocalHarnessGateScriptPath, mergeBaseMode);
        var error = Encoding.UTF8.GetString(result.StandardError);

        Assert.True(
            result.ExitCode == 1,
            $"expected exit 1, actual {result.ExitCode}\nstdout:\n{Encoding.UTF8.GetString(result.StandardOutput)}\nstderr:\n{error}");
        Assert.Contains(ExpectedMergeBaseDiagnostic(mergeBaseMode), error, StringComparison.Ordinal);
        if (mergeBaseMode == "candidate-failed")
        {
            Assert.DoesNotContain("BASE_ADVANCED", error, StringComparison.Ordinal);
        }
    }

    [Theory]
    [InlineData(PreflightScriptPath)]
    [InlineData(LocalHarnessGateScriptPath)]
    public void BaseResolutionFailureDiagnosticsCarryResolvedAndEmptyValues(string scriptPath)
    {
        if (OperatingSystem.IsWindows()) return;

        var result = RunInvalidMergeBase(scriptPath, "base-ref-failed");
        var error = Encoding.UTF8.GetString(result.StandardError);

        Assert.Equal(1, result.ExitCode);
        Assert.Contains(ExpectedMergeBaseDiagnostic("base-ref-failed"), error, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(GateBaseTipSha, false)]
    [InlineData("base", true)]
    public void LocalHarnessGateResolvesSymbolicAndFullOidBaseTipsToFork(
        string baseArgument,
        bool expectAdvanceAdvisory)
    {
        if (OperatingSystem.IsWindows()) return;

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
        WriteHarnessGateChainReportPair(candidateRoot);
        WriteHarnessGateChainDotnetShim(binDirectory);
        WriteExecutable(Path.Combine(binDirectory, "lake"), "#!/usr/bin/env bash\nexit 0");
        WriteObservedBaseGitShim(binDirectory, candidateRoot, baseArgument);

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

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static ProcessOutput RunInvalidMergeBase(string scriptPath, string mergeBaseMode)
    {
        var root = TestRepositoryLayout.FindRoot();
        using var fixture = new TemporaryDirectory();
        var candidateRoot = Path.Combine(fixture.Path, "candidate");
        var homeDirectory = Path.Combine(fixture.Path, "home");
        var binDirectory = Path.Combine(homeDirectory, ".dotnet");
        Directory.CreateDirectory(binDirectory);
        CopyAdmissionBaseLibraryIfPresent(candidateRoot);
        CopyResourceObservationLibrary(candidateRoot);
        WriteInvalidMergeBaseGitShim(binDirectory, candidateRoot);
        WriteExecutable(
            Path.Combine(binDirectory, "dotnet"),
            "#!/usr/bin/env bash\n[[ \"${1:-}\" == --version ]] && exit 0\n[[ \"${1:-}\" == restore ]] && exit 0\nexit 0");
        WriteExecutable(
            Path.Combine(binDirectory, "lake"),
            "#!/usr/bin/env bash\n[[ \"${1:-}\" == --version ]] && exit 0\nexit 0");
        WriteExecutable(Path.Combine(binDirectory, "make"), "#!/usr/bin/env bash\nexit 0");

        var command = scriptPath == PreflightScriptPath
            ? "HOME=\"$1\" BASE=\"$2\" PATH=\"$3:/usr/bin:/bin\" MERGE_BASE_MODE=\"$4\" exec /bin/bash \"$5\""
            : "HOME=\"$1\" PATH=\"$3:/usr/bin:/bin\" MERGE_BASE_MODE=\"$4\" exec /bin/bash \"$5\" --candidate \"$6\" --base \"$2\" --skip-engineering";
        return TestProcessRunner.Run(
            "/bin/bash",
            [
                "-c",
                command,
                "invalid-merge-base",
                homeDirectory,
                GateBaseTipSha,
                binDirectory,
                mergeBaseMode,
                Path.Combine(root, scriptPath),
                candidateRoot,
            ],
            candidateRoot,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);
    }

    private static string ExpectedMergeBaseDiagnostic(string mergeBaseMode)
    {
        var reason = mergeBaseMode switch
        {
            "candidate-failed" => "candidate-resolution-failed",
            "command-failed" => "merge-base-command-failed",
            "empty" => "merge-base-empty",
            "zero" => "merge-base-empty",
            "vacuous" => "vacuous",
            "base-ref-failed" => "base-tip-resolution-failed",
            _ => throw new ArgumentOutOfRangeException(nameof(mergeBaseMode)),
        };
        var candidate = mergeBaseMode == "candidate-failed" ? "empty" : GateCandidateSha;
        var resolvedBase = mergeBaseMode switch
        {
            "vacuous" => GateCandidateSha,
            "zero" => "0000000000000000000000000000000000000000",
            _ => "empty",
        };
        var baseTip = mergeBaseMode is "base-ref-failed" or "candidate-failed"
            ? "empty"
            : GateBaseTipSha;
        return $"BASE_RESOLUTION_FAILED reason={reason} BASE_REF={GateBaseTipSha} "
            + $"BASE_TIP_SHA={baseTip} CANDIDATE_SHA={candidate} BASE_SHA={resolvedBase}";
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static void WriteInvalidMergeBaseGitShim(string binDirectory, string candidateRoot) =>
        WriteExecutable(
            Path.Combine(binDirectory, "git"),
            $$"""
            #!/usr/bin/env bash
            if [[ "${1:-}" == -C ]]; then shift 2; fi
            case "$*" in
              "rev-parse --show-toplevel") printf '%s\n' '{{candidateRoot}}' ;;
              "rev-parse --verify HEAD"|"rev-parse --verify HEAD^{commit}")
                [[ "$MERGE_BASE_MODE" != candidate-failed ]] || exit 1
                printf '%s\n' '{{GateCandidateSha}}'
                ;;
              "rev-parse --verify {{GateBaseTipSha}}^{commit}")
                [[ "$MERGE_BASE_MODE" != base-ref-failed ]] || exit 1
                printf '%s\n' '{{GateBaseTipSha}}'
                ;;
              "merge-base {{GateBaseTipSha}} {{GateCandidateSha}}")
                case "$MERGE_BASE_MODE" in
                  command-failed) exit 1 ;;
                  empty) exit 0 ;;
                  zero) printf '%040d\n' 0 ;;
                  vacuous) printf '%s\n' '{{GateCandidateSha}}' ;;
                  *) exit 89 ;;
                esac
                ;;
              "merge-base --is-ancestor {{GateBaseTipSha}} {{GateCandidateSha}}") exit 0 ;;
              *) echo "unexpected git invocation: $*" >&2; exit 90 ;;
            esac
            """);

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static void WriteHarnessGateChainGitShim(string binDirectory, string candidateRoot) =>
        WriteExecutable(
            Path.Combine(binDirectory, "git"),
            $$"""
            #!/usr/bin/env bash
            if [[ "${1:-}" == -C ]]; then shift 2; fi
            case "$*" in
              "rev-parse --show-toplevel") printf '%s\n' '{{candidateRoot}}' ;;
              "rev-parse --verify base^{commit}"|"rev-parse --verify 0000000000000000000000000000000000000001^{commit}") printf '%040d\n' 1 ;;
              "rev-parse --verify HEAD^{commit}"|"rev-parse --verify HEAD"|"rev-parse HEAD") printf '%040d\n' 2 ;;
              "rev-parse HEAD^1") printf '%040d\n' 1 ;;
              "merge-base 0000000000000000000000000000000000000001 0000000000000000000000000000000000000002") printf '%040d\n' 1 ;;
              "merge-base --is-ancestor "*) exit 0 ;;
              "cat-file -e {{GateForkSha}}^{commit}"|"diff --name-only --no-renames -z {{GateForkSha}} --"|"ls-files --others --exclude-standard -z") exit 0 ;;
              *) echo "unexpected git invocation: $*" >&2; exit 90 ;;
            esac
            """);

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static void WriteObservedBaseGitShim(
        string binDirectory,
        string candidateRoot,
        string baseArgument) =>
        WriteExecutable(
            Path.Combine(binDirectory, "git"),
            $$"""
            #!/usr/bin/env bash
            if [[ "${1:-}" == -C ]]; then shift 2; fi
            case "$*" in
              "rev-parse --verify HEAD"|"rev-parse --verify HEAD^{commit}") printf '%s\n' '{{GateCandidateSha}}' ;;
              "rev-parse --verify {{baseArgument}}^{commit}")
                if [[ '{{baseArgument}}' == base ]]; then
                  count="$(cat "$GATE_BASE_REF_COUNT" 2>/dev/null || printf 0)"
                  count="$((count + 1))"
                  printf '%s\n' "$count" > "$GATE_BASE_REF_COUNT"
                  if [[ "$count" -ge 2 ]]; then
                    printf '%s\n' '{{GateAdvancedBaseTipSha}}'
                  else
                    printf '%s\n' '{{GateBaseTipSha}}'
                  fi
                else
                  printf '%s\n' '{{GateBaseTipSha}}'
                fi
                ;;
              "merge-base {{GateBaseTipSha}} {{GateCandidateSha}}") printf '%s\n' '{{GateForkSha}}' ;;
              *) echo "unexpected git invocation: $*" >&2; exit 90 ;;
            esac
            """);

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static void WriteHarnessGateChainForkPointGitShim(
        string binDirectory,
        string candidateRoot,
        string baseTipSha,
        string candidateSha,
        string forkSha,
        bool diverged) =>
        WriteExecutable(
            Path.Combine(binDirectory, "git"),
            $$"""
            #!/usr/bin/env bash
            if [[ "${1:-}" == -C ]]; then shift 2; fi
            case "$*" in
              "rev-parse --show-toplevel") printf '%s\n' '{{candidateRoot}}' ;;
              "rev-parse --verify base^{commit}") printf '%s\n' '{{baseTipSha}}' ;;
              "rev-parse --verify {{forkSha}}^{commit}") printf '%s\n' '{{forkSha}}' ;;
              "rev-parse --verify HEAD^{commit}"|"rev-parse --verify HEAD"|"rev-parse HEAD") printf '%s\n' '{{candidateSha}}' ;;
              "rev-parse HEAD^1") printf '%s\n' '{{forkSha}}' ;;
              "merge-base {{baseTipSha}} {{candidateSha}}") printf '%s\n' '{{forkSha}}' ;;
              "merge-base {{forkSha}} {{candidateSha}}") printf '%s\n' '{{forkSha}}' ;;
              "merge-base --is-ancestor {{baseTipSha}} {{candidateSha}}") exit {{(diverged ? 1 : 0)}} ;;
              "merge-base --is-ancestor {{forkSha}} {{candidateSha}}") exit 0 ;;
              "cat-file -e {{forkSha}}^{commit}"|"diff --name-only --no-renames -z {{forkSha}} --"|"ls-files --others --exclude-standard -z") exit 0 ;;
              merge\ *) printf 'mutated\n' > "$PREFLIGHT_GIT_STATE" ;;
              *) echo "unexpected git invocation: $*" >&2; exit 90 ;;
            esac
            """);

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static void WriteHarnessGateChainDotnetShim(string binDirectory) =>
        WriteExecutable(
            Path.Combine(binDirectory, "dotnet"),
            """
            #!/usr/bin/env bash
            case "${1:-}" in
              --version|restore) exit 0 ;;
              build)
                if [[ "$*" == *BannedApiCompileFailProof.csproj* ]]; then
                  while IFS=: read -r line _; do
                    printf '%s(%s,1): error RS0030: fixture banned API\n' \
                      'tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs' "$line" >&2
                  done < <(grep -nF '// banned-api-proof' \
                    tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs)
                  exit 1
                fi
                [[ "$*" != *CompileFailProof.csproj* ]] || exit 1
                exit 0
                ;;
              msbuild)
                project_root="${2%%/tools/*}"
                printf '%s/bin/candidate.dll\n' "$project_root"
                exit 0
                ;;
            esac
            if [[ "${2:-}" == selftest ]]; then printf 'selftest\n'; exit 0; fi
            if [[ "${2:-}" == check ]]; then
              if [[ -n "${PREFLIGHT_EXPECTED_GATE_BASE:-}" && "$*" != *" --protected-base $PREFLIGHT_EXPECTED_GATE_BASE "* ]]; then exit 94; fi
              exit "$PREFLIGHT_ADMISSION_RC"
            fi
            if [[ "${2:-}" == filemap-conform ]]; then exit 0; fi
            if [[ "$*" == *StrataLint.Scribe.csproj* && "$*" == *" --check"* ]]; then exit 0; fi
            echo "unexpected dotnet invocation: $*" >&2
            exit 91
            """);

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static void WriteHarnessGateChainMakeShim(string binDirectory) =>
        WriteExecutable(
            Path.Combine(binDirectory, "make"),
            """
            #!/usr/bin/env bash
            target=""
            gate_args=""
            gate_base=""
            for arg in "$@"; do
              case "$arg" in
                gate|dotnet|lean-report|test|engineering-tests|selftest) target="$arg" ;;
                GATE_ARGS=*) gate_args="${arg#GATE_ARGS=}" ;;
                BASE=*) gate_base="${arg#BASE=}" ;;
              esac
            done
            if [[ "$target" == lean-report ]]; then
              report="$PREFLIGHT_CANDIDATE_ROOT/.lake/build/stratalint/raw-lean-report.json"
              mkdir -p "$(dirname "$report")"
              printf '{}\n' > "$report"
              exit 0
            fi
            [[ "$target" == gate ]] || exit 0
            [[ "$gate_args" == --skip-engineering ]] || exit 92
            if [[ -n "${PREFLIGHT_EXPECTED_GATE_BASE:-}" ]]; then
              [[ "$gate_base" == "$PREFLIGHT_EXPECTED_GATE_BASE" ]] || exit 93
            fi
            "$PREFLIGHT_LOCAL_GATE" \
              --candidate "$PREFLIGHT_CANDIDATE_ROOT" \
              --base 0000000000000000000000000000000000000001 \
              --skip-engineering
            """);

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static void WriteHarnessGateChainReportPair(string candidateRoot)
    {
        CopyAdmissionBaseLibraryIfPresent(candidateRoot);
        CopyResourceObservationLibrary(candidateRoot);
        CopyBannedApiCompileFailProof(candidateRoot);
        var gateDirectory = Path.Combine(candidateRoot, ".github", "scripts");
        Directory.CreateDirectory(gateDirectory);
        File.Copy(
            Path.Combine(TestRepositoryLayout.FindRoot(), ".github", "scripts", "harness-gate.sh"),
            Path.Combine(gateDirectory, "harness-gate.sh"));
        File.SetUnixFileMode(
            Path.Combine(gateDirectory, "harness-gate.sh"),
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var producerDirectory = Path.Combine(candidateRoot, "tools", "lean-inspector");
        Directory.CreateDirectory(producerDirectory);
        WriteExecutable(
            Path.Combine(producerDirectory, "inspect.sh"),
            "#!/usr/bin/env bash\nexit 0");
        File.WriteAllText(Path.Combine(producerDirectory, "Inspector.lean"), "fixture\n");
        var workflowDirectory = Path.Combine(candidateRoot, "tools", "scripts", "workflow");
        Directory.CreateDirectory(workflowDirectory);
        File.Copy(
            Path.Combine(TestRepositoryLayout.FindRoot(), ScribeContentChecksScriptPath),
            Path.Combine(workflowDirectory, "scribe-content-checks.sh"));
        var script = Path.Combine(candidateRoot, "tools", "scripts", "lean-report-pair.sh");
        WriteExecutable(
            script,
            """
            #!/usr/bin/env bash
            while [[ $# -gt 0 ]]; do
              case "$1" in
                --candidate-output) candidate_output="$2"; shift 2 ;;
                *) shift 2 ;;
              esac
            done
            mkdir -p "$(dirname "$candidate_output")"
            printf '{}\n' > "$candidate_output"
            """);
    }

    private static void CopyAdmissionBaseLibraryIfPresent(string candidateRoot)
    {
        var source = Path.Combine(TestRepositoryLayout.FindRoot(), AdmissionBaseScriptPath);
        if (!File.Exists(source)) return;

        var target = Path.Combine(candidateRoot, AdmissionBaseScriptPath);
        Directory.CreateDirectory(Path.GetDirectoryName(target)!);
        File.Copy(source, target, overwrite: true);
    }

    private static void CopyResourceObservationLibrary(string candidateRoot)
    {
        const string relativePath = "tools/scripts/lib/resource-observation-lib.sh";
        var source = Path.Combine(TestRepositoryLayout.FindRoot(), relativePath);
        var target = Path.Combine(candidateRoot, relativePath);
        Directory.CreateDirectory(Path.GetDirectoryName(target)!);
        File.Copy(source, target, overwrite: true);
    }

    private static void CopyBannedApiCompileFailProof(string candidateRoot)
    {
        const string proofPath = "tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs";
        var source = Path.Combine(TestRepositoryLayout.FindRoot(), proofPath);
        var target = Path.Combine(candidateRoot, proofPath);
        Directory.CreateDirectory(Path.GetDirectoryName(target)!);
        File.Copy(source, target, overwrite: true);
    }
}
