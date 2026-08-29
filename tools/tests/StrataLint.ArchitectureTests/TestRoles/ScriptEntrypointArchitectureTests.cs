using System.Text.RegularExpressions;
using StrataLint.Tests;

namespace StrataLint.ArchitectureTests;

public sealed class ScriptEntrypointArchitectureTests
{
    private const string ReportSupervisorScriptPath = "tools/scripts/report/report-supervisor.sh";
    private const string LeanReportPairScriptPath = "tools/scripts/lean-report-pair.sh";
    private const string LeanReportInputScriptPath = "tools/scripts/report/lean-report-input.sh";

    [Fact]
    public void CiAndLocalGateReuseCanonicalEntrypoints()
    {
        var workflow = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            ".github/workflows/ci.yml"));
        var localGate = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "tools/scripts/local-harness-gate.sh"));
        var preflight = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "tools/scripts/preflight.sh"));
        var sharedGate = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            ".github/scripts/harness-gate.sh"));
        var makefile = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "Makefile"));

        Assert.Contains("make -C candidate/tools dotnet", workflow, StringComparison.Ordinal);
        Assert.Contains("make -C candidate/tools engineering-tests", workflow, StringComparison.Ordinal);
        Assert.Contains("make -C candidate/tools selftest", workflow, StringComparison.Ordinal);
        Assert.Contains("make -C \"$CANDIDATE_ROOT/tools\" dotnet", localGate, StringComparison.Ordinal);
        Assert.Contains("make -C \"$CANDIDATE_ROOT/tools\" test", localGate, StringComparison.Ordinal);
        Assert.Contains("make -C \"$CANDIDATE_ROOT/tools\" selftest", localGate, StringComparison.Ordinal);
        Assert.Contains("CI=true make -C tools dotnet", preflight, StringComparison.Ordinal);
        Assert.Contains(
            "CI=true STRATALINT_REQUIRE_LIVE_REPORT=1 make -C tools engineering-tests",
            preflight,
            StringComparison.Ordinal);
        Assert.Contains("make -C tools selftest", preflight, StringComparison.Ordinal);
        Assert.Contains("lean-report-pair.sh", localGate, StringComparison.Ordinal);
        Assert.DoesNotContain("--single", localGate, StringComparison.Ordinal);
        Assert.Contains("--skip-engineering", localGate, StringComparison.Ordinal);
        Assert.Contains("GATE_ARGS=\"--skip-engineering\"", preflight, StringComparison.Ordinal);
        Assert.DoesNotContain("refactor-pr-a-required", localGate, StringComparison.Ordinal);
        Assert.Contains("gate_stage_timing", localGate, StringComparison.Ordinal);
        Assert.Contains("gate_timing_summary", localGate, StringComparison.Ordinal);
        Assert.Contains("STRATALINT_TIMING", sharedGate, StringComparison.Ordinal);
        Assert.Contains("gate_stage_timing", sharedGate, StringComparison.Ordinal);
        Assert.Contains("mark restore-judge", sharedGate, StringComparison.Ordinal);
        Assert.Contains("mark build-judge", sharedGate, StringComparison.Ordinal);
        Assert.Contains("filemap-conform", sharedGate, StringComparison.Ordinal);
        Assert.DoesNotContain("filemap-conform", localGate, StringComparison.Ordinal);
        Assert.True(
            sharedGate.IndexOf("filemap-conform", StringComparison.Ordinal)
                > sharedGate.IndexOf(" check --protected-base", StringComparison.Ordinal));
        Assert.DoesNotContain("dotnet \"$JUDGE_DLL\" selftest", sharedGate, StringComparison.Ordinal);
        Assert.DoesNotContain("mark selftest", sharedGate, StringComparison.Ordinal);
        Assert.DoesNotContain("PrAEffectiveness", makefile, StringComparison.Ordinal);
        Assert.DoesNotContain("STRATALINT_TIMING:-1", sharedGate, StringComparison.Ordinal);
        Assert.Contains("$CANDIDATE_ROOT/.github/scripts/harness-gate.sh", localGate, StringComparison.Ordinal);
        Assert.Contains("$CANDIDATE_ROOT/tools/lean-inspector/inspect.sh", localGate, StringComparison.Ordinal);
        Assert.Contains("--candidate-lean-report", localGate, StringComparison.Ordinal);
        Assert.DoesNotContain("--baseline-lean-report", localGate, StringComparison.Ordinal);
        Assert.DoesNotContain("--frozen-evidence-root", localGate, StringComparison.Ordinal);
        Assert.DoesNotContain("--judge-root", localGate, StringComparison.Ordinal);
        Assert.DoesNotContain("worktree add", localGate, StringComparison.Ordinal);
        Assert.DoesNotContain("verify-conservative", sharedGate, StringComparison.Ordinal);
        Assert.DoesNotContain("make -C \"$CANDIDATE_ROOT\" dotnet", sharedGate, StringComparison.Ordinal);
        Assert.Contains("-getProperty:TargetPath", sharedGate, StringComparison.Ordinal);
        Assert.DoesNotContain("--baseline-harness", sharedGate, StringComparison.Ordinal);
        Assert.DoesNotContain("--candidate-harness", sharedGate, StringComparison.Ordinal);
        Assert.DoesNotContain("conservative-certificate", sharedGate, StringComparison.Ordinal);
        Assert.Contains(
            "protected-surface change (SL-022); content checks passed",
            sharedGate,
            StringComparison.Ordinal);
        Assert.DoesNotContain("Bootstrap scaffold path", sharedGate, StringComparison.Ordinal);
        Assert.Contains("gate_rc", localGate, StringComparison.Ordinal);
        Assert.Contains("$gate_rc -eq 3", localGate, StringComparison.Ordinal);
        Assert.Contains(
            "local-harness-gate: protected-surface change (SL-022)",
            localGate,
            StringComparison.Ordinal);
        Assert.DoesNotContain("certified SL-022", localGate, StringComparison.Ordinal);
        Assert.Contains("$rc\" -ne 0 && \"$rc\" -ne 3", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("conservative extension", workflow, StringComparison.OrdinalIgnoreCase);
        Assert.DoesNotContain("golden-record", workflow, StringComparison.Ordinal);
        Assert.Contains("|| true", localGate, StringComparison.Ordinal);
        Assert.Contains("|| true", preflight, StringComparison.Ordinal);
        Assert.Contains(">> \"$LOCAL_TIMING_FILE\" || true", localGate, StringComparison.Ordinal);
    }

    [Fact]
    public void AdmissionEntrypointsDelegateForkResolutionToOneLibrary()
    {
        var preflight = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "tools/scripts/preflight.sh"));
        var localGate = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "tools/scripts/local-harness-gate.sh"));
        var admissionBase = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "tools/scripts/lib/admission-base-lib.sh"));

        const string source = "source \"$ROOT/tools/scripts/lib/admission-base-lib.sh\"";
        const string preflightResolve = "admission_resolve_base \"$ROOT\" \"$BASE_REF\"";
        const string localResolve =
            "admission_resolve_base \"$CANDIDATE_ROOT\" \"$BASE_REF\"";
        string[] ordered = ["ROOT=\"$(git rev-parse --show-toplevel)\"", source, "fetch --prune", preflightResolve, "CI=true make -C tools dotnet"];
        var cursor = -1;
        foreach (var fragment in ordered)
        {
            cursor = preflight.IndexOf(fragment, cursor + 1, StringComparison.Ordinal);
            Assert.True(cursor >= 0, $"preflight contract is absent or out of order: {fragment}");
        }
        Assert.Contains(source, localGate, StringComparison.Ordinal);
        Assert.Contains(localResolve, localGate, StringComparison.Ordinal);
        Assert.DoesNotContain("BASE_RESOLUTION_FAILED", preflight, StringComparison.Ordinal);
        Assert.DoesNotContain("BASE_RESOLUTION_FAILED", localGate, StringComparison.Ordinal);
        Assert.Single(Regex.Matches(admissionBase, "BASE_RESOLUTION_FAILED").Cast<Match>());
        Assert.Single(Regex.Matches(
            admissionBase,
            "\\bgit\\s+-C\\s+\"\\$repository_root\"\\s+merge-base\\b").Cast<Match>());
        Assert.DoesNotContain("git merge-base", preflight, StringComparison.Ordinal);
        Assert.DoesNotContain("git -C \"$CANDIDATE_ROOT\" merge-base", localGate, StringComparison.Ordinal);
        Assert.DoesNotContain("merge-base --is-ancestor", preflight, StringComparison.Ordinal);
        Assert.Contains("make gate BASE=\"$BASE_SHA\"", preflight, StringComparison.Ordinal);
        Assert.Contains("\"$observed_base\" != \"$BASE_TIP_SHA\"", preflight, StringComparison.Ordinal);
        Assert.Contains("|| true", preflight[preflight.IndexOf("BASE_ADVANCED", StringComparison.Ordinal)..], StringComparison.Ordinal);
        Assert.DoesNotContain("merge-base --is-ancestor", localGate, StringComparison.Ordinal);
        Assert.DoesNotContain("pinned base is not a strict ancestor", localGate, StringComparison.Ordinal);
    }

    [Fact]
    public void CiChecksOutCandidateTreesOnlyAndCarriesBaseAsSha()
    {
        var workflow = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            ".github/workflows/ci.yml"));

        Assert.Equal(3, Regex.Matches(workflow, "uses: actions/checkout@v4").Count);
        Assert.DoesNotContain("path: baseline", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("Check out content-addressed dev baseline", workflow, StringComparison.Ordinal);
        Assert.Contains("baseline_sha: ${{ steps.base.outputs.sha }}", workflow, StringComparison.Ordinal);
        Assert.Contains("DEV_BASELINE_SHA: ${{ needs.lean-inspect.outputs.baseline_sha }}", workflow, StringComparison.Ordinal);
    }

    [Fact]
    public void ReportEntrypointsDelegateToTheSingleHostSupervisor()
    {
        var supervisorName = Path.GetFileName(ReportSupervisorScriptPath);
        var pairName = Path.GetFileName(LeanReportPairScriptPath);
        var producer = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "tools/scripts/report/lean-report.sh"));
        var pair = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "tools/scripts/lean-report-pair.sh"));
        var consumer = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "tools/scripts/report/report-consumer.sh"));

        Assert.Contains(pairName, producer, StringComparison.Ordinal);
        Assert.Contains(supervisorName, pair, StringComparison.Ordinal);
        Assert.Contains("--lean-slot", pair, StringComparison.Ordinal);
        Assert.Contains(supervisorName, consumer, StringComparison.Ordinal);
        Assert.Contains(LeanReportInputScriptPath, consumer, StringComparison.Ordinal);
        Assert.DoesNotContain("mktemp", producer, StringComparison.Ordinal);
        Assert.Contains("mktemp", consumer, StringComparison.Ordinal);
        Assert.Contains("STRATALINT_LEAN_REPORT", consumer, StringComparison.Ordinal);
        Assert.Contains(".materials.zip", consumer, StringComparison.Ordinal);
        Assert.DoesNotContain("may be stale", consumer, StringComparison.Ordinal);
    }

    [Fact]
    public void RepositoryDoesNotWalkTheLeanCacheTreePerFile()
    {
        // A per-file clone walk costs one system call per entry. Build the rejected forms
        // dynamically so this repository-wide guard does not match its own source.
        var cloneFlag = string.Concat('-', 'c');
        var recursiveFlag = string.Concat('-', 'R');
        var shellForm = $"cp {cloneFlag}";
        var argumentForm = $"\"{cloneFlag}\", \"{recursiveFlag}\"";
        var scan = TestProcessRunner.Run(
            "git",
            ["grep", "-n", "-I", "-e", shellForm, "-e", argumentForm, "--", "."],
            TestRepositoryLayout.FindRoot(),
            BoundedProcessRunner.HangDetectionBudget,
            1024 * 1024);

        Assert.Equal(1, scan.ExitCode);
    }
}
