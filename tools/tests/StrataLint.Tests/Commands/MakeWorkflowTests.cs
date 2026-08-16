using System.Text.RegularExpressions;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class MakeWorkflowTests
{
    private const string DotnetBuildScriptPath = "tools/scripts/dotnet-build.sh";
    private const string ScribeScriptPath = "tools/scripts/scribe.sh";
    private const string SelftestScriptPath = "tools/scripts/stratalint-selftest.sh";
    private const string LocalHarnessGateScriptPath =
        "tools/scripts/local-harness-gate.sh";
    private const string PreflightScriptPath = "tools/scripts/preflight.sh";
    private const string AdmissionBaseScriptPath =
        "tools/scripts/lib/admission-base-lib.sh";
    private const string ScribeContentChecksScriptPath =
        "tools/scripts/workflow/scribe-content-checks.sh";
    private const string InstallLeanToolchainScriptPath =
        "tools/scripts/workflow/install-lean-toolchain.sh";
    private const string CleanLanesScriptPath = "tools/scripts/clean-lanes.sh";
    private const string WorktreeInitScriptPath = "tools/scripts/worktree-init.sh";
    private const string LeanReportScriptPath =
        "tools/scripts/report/lean-report.sh";
    private const string LeanCacheEnsureScriptPath =
        "tools/scripts/worktree/lean-cache-ensure.sh";
    private const string LeanCacheRunScriptPath =
        "tools/scripts/worktree/lean-cache-run.sh";
    private const string IngestScriptPath = "tools/scripts/ingest.sh";
    private const string TheoryIngestClosureScriptPath = "tools/scripts/workflow/theory-ingest-closure.sh";
    private const string EchoResidualSummaryScriptPath =
        "tools/scripts/report/echo-residual-summary.sh";
    private const string ReportConsumerScriptPath =
        "tools/scripts/report/report-consumer.sh";
    private const string ReportSupervisorScriptPath =
        "tools/scripts/report/report-supervisor.sh";
    private const string LeanReportInputScriptPath =
        "tools/scripts/report/lean-report-input.sh";
    private const string LeanReportPairScriptPath = "tools/scripts/lean-report-pair.sh";
    private const string PerfReportScriptPath = "tools/scripts/perf-report.sh";
    private const string PerfEventScriptPath = "tools/scripts/lib/perf-event-lib.sh";
    private const string ToolsMakefilePath = "tools/Makefile";
    private const string AdmissionWorkflowPath = ".github/workflows/ci.yml";
    private const string TheoryIngestWorkflowPath = ".github/workflows/theory-ingest.yml";
    private const string PrOpenScriptPath = "tools/scripts/pr.sh open";

    private static readonly string[] RootTargets =
    [
        "help",
        "test",
        "lean-cache-ensure",
        "lean",
        "lean-report",
        "build",
        "emit",
        "ingest",
        "echo-residual-summary",
        "show-atom",
        "deliver-check",
        "receipts-stage",
        "deposit",
        "cover",
        "worktree",
        "pr-open",
        "preflight",
        "gate",
    ];

    private static readonly string[] ToolsTargets =
    [
        "help",
        "dotnet",
        "test",
        "selftest",
        "perf-report",
        "clean-lanes",
    ];

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

        var result = BoundedProcessRunner.Run(
            "/bin/bash",
            ["-c", "PATH=\"$1:$PATH\" exec make --no-print-directory echo-residual-summary BASE=synthetic-base", "echo-make", binDirectory],
            fixture.Path,
            TimeSpan.FromSeconds(30),
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
    public void CiAndLocalGateReuseCanonicalEntrypoints()
    {
        var root = TestRepositoryLayout.FindRoot();
        var workflow = File.ReadAllText(Path.Combine(root, ".github", "workflows", "ci.yml"));
        var localGate = File.ReadAllText(Path.Combine(root, LocalHarnessGateScriptPath));
        var preflight = File.ReadAllText(Path.Combine(root, PreflightScriptPath));
        var sharedGate = File.ReadAllText(Path.Combine(root, ".github", "scripts", "harness-gate.sh"));
        var perfEvents = File.ReadAllText(Path.Combine(root, PerfEventScriptPath));
        var makefile = File.ReadAllText(Path.Combine(root, "Makefile"));

        Assert.Contains("make -C candidate/tools dotnet", workflow, StringComparison.Ordinal);
        Assert.Contains("make -C candidate/tools test", workflow, StringComparison.Ordinal);
        Assert.Contains("make -C candidate/tools selftest", workflow, StringComparison.Ordinal);
        Assert.Contains("make -C \"$CANDIDATE_ROOT/tools\" dotnet", localGate, StringComparison.Ordinal);
        Assert.Contains("make -C \"$CANDIDATE_ROOT/tools\" test", localGate, StringComparison.Ordinal);
        Assert.Contains("make -C \"$CANDIDATE_ROOT/tools\" selftest", localGate, StringComparison.Ordinal);
        Assert.Contains("CI=true make -C tools dotnet", preflight, StringComparison.Ordinal);
        Assert.Contains(
            "CI=true STRATALINT_REQUIRE_LIVE_REPORT=1 make -C tools test",
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
        Assert.Contains("stratalint-perf-event-v1", perfEvents, StringComparison.Ordinal);
        Assert.Contains("loadavg_per_cpu", perfEvents, StringComparison.Ordinal);
        Assert.Contains("host_concurrency", perfEvents, StringComparison.Ordinal);
        Assert.Contains("disk_free_gb", perfEvents, StringComparison.Ordinal);
        Assert.Contains("perf_capture_event", localGate, StringComparison.Ordinal);
        Assert.Contains("perf_flush_events", localGate, StringComparison.Ordinal);
        Assert.Contains("perf_capture_event", preflight, StringComparison.Ordinal);
        Assert.Contains("perf_flush_events", preflight, StringComparison.Ordinal);
        Assert.Contains("perf_capture_event", localGate + preflight, StringComparison.Ordinal);
        Assert.Contains("|| true", localGate, StringComparison.Ordinal);
        Assert.Contains("|| true", preflight, StringComparison.Ordinal);
        Assert.Contains(">> \"$LOCAL_TIMING_FILE\" || true", localGate, StringComparison.Ordinal);
    }

    [Fact]
    public void PreflightRefreshesLeanReportAfterDotnetAndBeforeTests()
    {
        var root = TestRepositoryLayout.FindRoot();
        var preflight = File.ReadAllText(Path.Combine(root, PreflightScriptPath));

        var dotnetIndex = preflight.IndexOf("CI=true make -C tools dotnet", StringComparison.Ordinal);
        var leanReportIndex = preflight.IndexOf("make lean-report", StringComparison.Ordinal);
        var testIndex = preflight.IndexOf(
            "CI=true STRATALINT_REQUIRE_LIVE_REPORT=1 make -C tools test",
            StringComparison.Ordinal);

        Assert.True(dotnetIndex >= 0, "preflight must build the .NET report consumer");
        Assert.True(leanReportIndex >= 0, "preflight must refresh the raw Lean report");
        Assert.True(testIndex >= 0, "preflight must run the harness tests");
        Assert.True(dotnetIndex < leanReportIndex, "the .NET build must precede report production");
        Assert.True(leanReportIndex < testIndex, "report production must precede every test consumer");
    }

    [Fact]
    public void AdmissionEntrypointsDelegateForkResolutionToOneLibrary()
    {
        var root = TestRepositoryLayout.FindRoot();
        var preflight = File.ReadAllText(Path.Combine(root, PreflightScriptPath));
        var localGate = File.ReadAllText(Path.Combine(root, LocalHarnessGateScriptPath));
        var admissionBase = File.ReadAllText(Path.Combine(root, AdmissionBaseScriptPath));

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
        var workflow = File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), AdmissionWorkflowPath));

        Assert.Equal(3, Regex.Matches(workflow, "uses: actions/checkout@v4").Count);
        Assert.DoesNotContain("path: baseline", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("Check out content-addressed dev baseline", workflow, StringComparison.Ordinal);
        Assert.Contains("baseline_sha: ${{ steps.base.outputs.sha }}", workflow, StringComparison.Ordinal);
        Assert.Contains("DEV_BASELINE_SHA: ${{ needs.lean-inspect.outputs.baseline_sha }}", workflow, StringComparison.Ordinal);
    }

    [Fact]
    public void TheoryIngestRunsCandidateIngestWithMergeBaseAndSharedCaches()
    {
        var root = TestRepositoryLayout.FindRoot();
        var admission = File.ReadAllText(Path.Combine(root, AdmissionWorkflowPath));
        var workflow = File.ReadAllText(Path.Combine(root, TheoryIngestWorkflowPath));
        var runnerIndex = workflow.IndexOf("runs-on: ubuntu-24.04-arm", StringComparison.Ordinal);
        var addressIndex = workflow.IndexOf(
            "- name: Resolve candidate canonical Lean report address",
            StringComparison.Ordinal);
        var restoreIndex = workflow.IndexOf(
            "- name: Restore candidate canonical Lean report",
            StringComparison.Ordinal);
        var verifyIndex = workflow.IndexOf(
            "- name: Install and verify candidate canonical Lean report",
            StringComparison.Ordinal);
        var baseIndex = workflow.IndexOf("- name: Resolve merge-base SHA", StringComparison.Ordinal);
        var ingestIndex = workflow.IndexOf("          make ingest BASE=${{ steps.base.outputs.sha }}\n", StringComparison.Ordinal);

        Assert.True(runnerIndex >= 0, "theory ingest must use the arm runner");
        Assert.True(baseIndex >= 0, "theory ingest must resolve a merge-base SHA");
        Assert.True(addressIndex > baseIndex, "report address must follow base resolution");
        Assert.True(restoreIndex > addressIndex, "report restore must use the resolved address");
        Assert.True(verifyIndex > restoreIndex, "restored report must be verified before consumption");
        Assert.True(ingestIndex > verifyIndex, "ingest must only consume a verified canonical report");

        Assert.Contains("uses: actions/cache/save@v4", admission, StringComparison.Ordinal);
        Assert.Contains("uses: actions/cache/restore@v4", workflow, StringComparison.Ordinal);
        // 不变量是「两个 workflow 共用**同一个** key 字符串」,不是「只出现一次」——
        // 证据:ingest 侧本来就带 .Distinct(),因为它 restore 与其它步骤可共用同一 key。
        // admission 侧此前只有 save 一处,故省了 Distinct;现在它也 restore 同一个 key
        // (关键路径复用报告),两侧遂对称。保留的判据仍是「distinct key 恰好一个且两侧相等」。
        var admissionJob = admission.Split("  lean-inspect:\n", StringSplitOptions.None)[1]
            .Split("  baseline-admission:\n", StringSplitOptions.None)[0];
        var admissionCacheKey = Assert.Single(
            admissionJob.Split('\n')
                .Where(static line => line.TrimStart().StartsWith(
                    "key: stratalint-canonical-lean-report-v2-",
                    StringComparison.Ordinal))
                .Select(static line => line.Trim())
                .Distinct());
        var ingestCacheKey = Assert.Single(
            workflow.Split('\n')
                .Where(static line => line.TrimStart().StartsWith(
                    "key: stratalint-canonical-lean-report-v2-",
                    StringComparison.Ordinal))
                .Select(static line => line.Trim())
                .Distinct());
        Assert.Equal(admissionCacheKey, ingestCacheKey);

        var producerIndex = workflow.IndexOf(
            "- name: Produce candidate canonical Lean report on cache miss",
            StringComparison.Ordinal);
        var producerEndIndex = workflow.IndexOf(
            "      - name: ",
            producerIndex + "      - name: ".Length,
            StringComparison.Ordinal);
        Assert.True(producerIndex > restoreIndex, "a cache miss must produce in the ingest job");
        Assert.True(producerEndIndex > producerIndex, "the cache-miss producer must be a bounded step");
        Assert.True(verifyIndex > producerIndex, "both restored and fresh reports must be verified");
        Assert.Contains(
            "timeout-minutes: 30",
            workflow[producerIndex..producerEndIndex],
            StringComparison.Ordinal);
        Assert.Single(Regex.Matches(workflow, "id: lean-report-cache"));
        Assert.Single(Regex.Matches(workflow, "key: stratalint-canonical-lean-report-v2-"));
        Assert.Contains("steps.lean-report-cache.outputs.cache-hit != 'true'", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("sleep " + "360", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("lookup-only: true", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("fail-on-cache-miss: true", workflow, StringComparison.Ordinal);
        Assert.Contains("steps.lean-report-input.outputs.address", admissionCacheKey, StringComparison.Ordinal);
        Assert.Contains(
            "$(basename \"$target\")\" > \"${target}.sha256\"",
            admission,
            StringComparison.Ordinal);
        Assert.Contains("steps.lean-report-cache.outputs.cache-hit", workflow, StringComparison.Ordinal);
        Assert.Contains(LeanReportInputScriptPath, workflow, StringComparison.Ordinal);
        Assert.Contains("\" verify \\", workflow, StringComparison.Ordinal);
        Assert.Contains(".lake/build/stratalint/raw-lean-report.json", workflow, StringComparison.Ordinal);
        Assert.Contains("timeout-minutes: 36", workflow, StringComparison.Ordinal);
        Assert.Contains("actions: read", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("          make lean\n", workflow, StringComparison.Ordinal);
        Assert.Contains("          make lean-report\n", workflow, StringComparison.Ordinal);
        Assert.Contains("Install pinned Lean toolchain on cache miss", workflow, StringComparison.Ordinal);
        Assert.Contains("Restore candidate Lean build artifacts on cache miss", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("uses: actions/cache@v4", workflow, StringComparison.Ordinal);
        AssertLakeCacheContract(admission, workflow);
    }

    [Fact]
    public void TheoryIngestRunsCandidateClosureWithoutOverlay()
    {
        var root = TestRepositoryLayout.FindRoot();
        var workflow = File.ReadAllText(Path.Combine(root, TheoryIngestWorkflowPath));
        Assert.Contains("contents: read", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("Enforce candidate data-only boundary", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("Enforce write-path whitelist and commit back", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("theory-ingest-bot", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("THEORY-INGEST-REGISTRY-001", workflow, StringComparison.Ordinal);
        var ingestIndex = workflow.IndexOf("make ingest BASE=${{ steps.base.outputs.sha }}", StringComparison.Ordinal);
        var closureIndex = workflow.IndexOf(TheoryIngestClosureScriptPath, StringComparison.Ordinal);
        Assert.True(ingestIndex >= 0, "ingest must receive the resolved merge-base SHA");
        Assert.True(closureIndex > ingestIndex, "closure must run after ingest");
        Assert.Contains("$GITHUB_WORKSPACE/candidate/" + TheoryIngestClosureScriptPath, workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("THEORY_INGEST_OVERLAY_PATHS", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("Overlay judge", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("rsync", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("--exclude", workflow, StringComparison.Ordinal);
    }

    [Fact]
    public void TheoryIngestNoLongerCarriesLegacyBoundaryOrWritebackContracts()
    {
        var root = TestRepositoryLayout.FindRoot();
        var workflow = File.ReadAllText(Path.Combine(root, TheoryIngestWorkflowPath));
        Assert.DoesNotContain("Enforce candidate data-only boundary", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("Enforce write-path whitelist and commit back", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("THEORY-INGEST-REGISTRY-001", workflow, StringComparison.Ordinal);
    }

    [Fact]
    public void TheoryIngestDoesNotRewriteEchoProjection()
    {
        var root = TestRepositoryLayout.FindRoot();
        var workflow = File.ReadAllText(Path.Combine(root, TheoryIngestWorkflowPath));
        Assert.DoesNotContain("Generated/echo-residuals", workflow, StringComparison.Ordinal);
    }

    [Fact]
    public void LocalGateHonorsExplicitTemporaryDirectory()
    {
        var root = TestRepositoryLayout.FindRoot();
        var localGate = File.ReadAllText(Path.Combine(root, LocalHarnessGateScriptPath));

        Assert.Contains(
            "mktemp -d \"${TMPDIR:-/tmp}/stratalint-local-gate.XXXXXXXX\"",
            localGate,
            StringComparison.Ordinal);
    }

    [Fact]
    public void ReportEntrypointsDelegateToTheSingleHostSupervisor()
    {
        var root = TestRepositoryLayout.FindRoot();
        var supervisorName = Path.GetFileName(ReportSupervisorScriptPath);
        var pairName = Path.GetFileName(LeanReportPairScriptPath);
        var producer = File.ReadAllText(Path.Combine(root, LeanReportScriptPath));
        var pair = File.ReadAllText(Path.Combine(root, LeanReportPairScriptPath));
        var consumer = File.ReadAllText(Path.Combine(root, ReportConsumerScriptPath));

        Assert.Contains(pairName, producer, StringComparison.Ordinal);
        Assert.Contains(supervisorName, pair, StringComparison.Ordinal);
        Assert.Contains("--lean-slot", pair, StringComparison.Ordinal);
        Assert.Contains(supervisorName, consumer, StringComparison.Ordinal);
        Assert.Contains(LeanReportInputScriptPath, consumer, StringComparison.Ordinal);
        Assert.DoesNotContain("mktemp", producer, StringComparison.Ordinal);
        Assert.Contains("mktemp", consumer, StringComparison.Ordinal);
        Assert.Contains("STRATALINT_LEAN_REPORT", consumer, StringComparison.Ordinal);
    }

    [Fact]
    public void ScribeWrapperConsumesOnlyAPrecomputedLeanReport()
    {
        var root = TestRepositoryLayout.FindRoot();
        var script = File.ReadAllText(Path.Combine(root, ScribeScriptPath));

        Assert.DoesNotContain("lean-inspector/inspect.sh", script, StringComparison.Ordinal);
        Assert.DoesNotContain("SCRIBE_USE_EXISTING_REPORT", script, StringComparison.Ordinal);
        Assert.Contains(ReportConsumerScriptPath, script, StringComparison.Ordinal);
        Assert.Contains("scribe-consumer", script, StringComparison.Ordinal);
        Assert.Contains(".lake/build/stratalint/raw-lean-report.json", script, StringComparison.Ordinal);
        Assert.DoesNotContain("CHECK_ARGS=()", script, StringComparison.Ordinal);
        Assert.Contains("emit|emit-values|filemap) run_scribe \"$1\"", script, StringComparison.Ordinal);
        Assert.Contains("generators=(emit emit-values filemap dag)", script, StringComparison.Ordinal);
        Assert.Contains("for generator in \"${generators[@]}\"", script, StringComparison.Ordinal);
    }

    [Fact]
    public void WorktreeAdapterPreservesTheCallerToolPathAndResolvesTheRepositoryRoot()
    {
        var root = TestRepositoryLayout.FindRoot();
        var script = File.ReadAllText(Path.Combine(root, WorktreeInitScriptPath));
        var dirnameIndex = script.IndexOf("dirname", StringComparison.Ordinal);
        var dotnetIndex = script.IndexOf("exec dotnet run", StringComparison.Ordinal);

        Assert.DoesNotContain("export PATH=", script, StringComparison.Ordinal);
        Assert.True(dirnameIndex >= 0, "worktree adapter must resolve its repository root");
        Assert.True(dotnetIndex > dirnameIndex, "repository root resolution must precede the CLI invocation");
    }

    [Fact]
    public void PerformanceJsonQuoteRemovesUnsupportedControlBytes()
    {
        var root = TestRepositoryLayout.FindRoot();
        var script = Path.Combine(root, PerfEventScriptPath);
        var result = BoundedProcessRunner.Run(
            "/bin/bash",
            [
                "-c",
                "source \"$1\"; perf_json_quote \"$2\"",
                "perf-json-quote",
                script,
                "run\u0001id",
            ],
            root,
            TimeSpan.FromSeconds(10),
            4 * 1024);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal("\"runid\"", System.Text.Encoding.UTF8.GetString(result.StandardOutput));
    }

    [Fact]
    public void PerformanceSpoolIgnoresATmpdirInsideTheRepository()
    {
        var root = TestRepositoryLayout.FindRoot();
        var script = Path.Combine(root, PerfEventScriptPath);
        using var repository = new TemporaryDirectory();
        var result = BoundedProcessRunner.Run(
            "/bin/bash",
            [
                "-c",
                "source \"$1\"; TMPDIR=\"$2\" perf_make_spool_dir \"$2\" stratalint-test-perf",
                "perf-spool",
                script,
                repository.Path,
            ],
            root,
            TimeSpan.FromSeconds(10),
            4 * 1024);
        var spool = System.Text.Encoding.UTF8.GetString(result.StandardOutput).Trim();

        try
        {
            Assert.Equal(0, result.ExitCode);
            Assert.True(Path.IsPathRooted(spool));
            Assert.False(
                Path.GetFullPath(spool).StartsWith(
                    Path.GetFullPath(repository.Path) + Path.DirectorySeparatorChar,
                    StringComparison.Ordinal));
        }
        finally
        {
            if (Directory.Exists(spool)) Directory.Delete(spool, recursive: true);
        }
    }

    private static int RecipeCount(string makefile, string target) =>
        RecipeLines(makefile, target).Count;

    private static string Recipe(string makefile, string target) =>
        Assert.Single(RecipeLines(makefile, target));

    private static IReadOnlyList<string> RecipeLines(string makefile, string target)
    {
        var lines = makefile.Split('\n');
        var start = Array.FindIndex(lines, line => line.StartsWith(target + ":", StringComparison.Ordinal));
        Assert.True(start >= 0, $"target is absent: {target}");
        return lines
            .Skip(start + 1)
            .TakeWhile(static line => line.Length == 0 || line[0] == '\t')
            .Where(static line => line.StartsWith('\t'))
            .ToArray();
    }

}
