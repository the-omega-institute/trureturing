using System.Text.RegularExpressions;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class MakeWorkflowTests
{
    private const string DotnetBuildScriptPath = "Meta/StrataLint/scripts/dotnet-build.sh";
    private const string ScribeScriptPath = "Meta/StrataLint/scripts/scribe.sh";
    private const string SelftestScriptPath = "Meta/StrataLint/scripts/stratalint-selftest.sh";
    private const string LocalHarnessGateScriptPath =
        "Meta/StrataLint/scripts/local-harness-gate.sh";
    private const string PreflightScriptPath = "Meta/StrataLint/scripts/preflight.sh";
    private const string CleanLanesScriptPath = "Meta/StrataLint/scripts/clean-lanes.sh";
    private const string WorktreeInitScriptPath = "Meta/StrataLint/scripts/worktree-init.sh";
    private const string LeanReportScriptPath =
        "Meta/StrataLint/scripts/report/lean-report.sh";
    private const string LeanCacheEnsureScriptPath =
        "Meta/StrataLint/scripts/worktree/lean-cache-ensure.sh";
    private const string IngestScriptPath = "Meta/StrataLint/scripts/ingest.sh";
    private const string TheoryIngestClosureScriptPath = "Meta/StrataLint/scripts/workflow/theory-ingest-closure.sh";
    private const string EchoResidualSummaryScriptPath =
        "Meta/StrataLint/scripts/report/echo-residual-summary.sh";
    private const string ReportConsumerScriptPath =
        "Meta/StrataLint/scripts/report/report-consumer.sh";
    private const string ReportSupervisorScriptPath =
        "Meta/StrataLint/scripts/report/report-supervisor.sh";
    private const string LeanReportInputScriptPath =
        "Meta/StrataLint/scripts/report/lean-report-input.sh";
    private const string LeanReportPairScriptPath = "Meta/StrataLint/scripts/lean-report-pair.sh";
    private const string PerfReportScriptPath = "Meta/StrataLint/scripts/perf-report.sh";
    private const string PerfEventScriptPath = "Meta/StrataLint/scripts/perf-event-lib.sh";
    private const string AdmissionWorkflowPath = ".github/workflows/ci.yml";
    private const string TheoryIngestWorkflowPath = ".github/workflows/theory-ingest.yml";
    private const string PrOpenScriptPath = "Meta/StrataLint/scripts/pr.sh open";
    private const string PrUpdateScriptPath = "Meta/StrataLint/scripts/pr.sh update";

    private static readonly string[] Targets =
    [
        "help",
        "dotnet",
        "test",
        "test-harness",
        "test-all",
        "lean-cache-ensure",
        "lean",
        "lean-report",
        "build",
        "clean-lanes",
        "emit",
        "ingest",
        "echo-residual-summary",
        "selftest",
        "scratch-sweep",
        "gate",
        "perf-report",
        "deliver-check",
        "receipts-stage",
        "derived-refresh",
        "deposit",
        "cover",
        "show-atom",
        "worktree",
        "pr-open",
        "pr-update",
        "refactor-p0-0-gate-authority",
    ];

    [Fact]
    public void EchoResidualSummaryRunsMakeAndKeepsDiagnosticsOutOfThePasteableBlock()
    {
        if (OperatingSystem.IsWindows()) return;

        var root = FindRepositoryRoot();
        using var fixture = new TemporaryDirectory();
        var reportDirectory = Path.Combine(fixture.Path, "Meta", "StrataLint", "scripts", "report");
        var cliDirectory = Path.Combine(fixture.Path, "Meta", "StrataLint", "StrataLint.Cli");
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
    public void EchoProjectionUsesTheFileMapShardGlobNotRegistryInstances()
    {
        var root = FindRepositoryRoot();
        var registry = File.ReadAllText(Path.Combine(root, "Meta", "registry.yaml"));
        var fileMap = File.ReadAllText(Path.Combine(root, "Meta", "FILEMAP.toml"));
        var gitignore = File.ReadAllText(Path.Combine(root, ".gitignore"));

        Assert.DoesNotContain("Generated/echo-residual", registry, StringComparison.Ordinal);
        Assert.Contains("pattern = \"Generated/echo-residuals/*.md\"", fileMap, StringComparison.Ordinal);
        Assert.Contains(".echo-review.md", gitignore, StringComparison.Ordinal);
        Assert.Contains(".sshx-*", gitignore, StringComparison.Ordinal);
    }

    [Fact]
    public void CiAndLocalGateReuseCanonicalEntrypoints()
    {
        var root = FindRepositoryRoot();
        var workflow = File.ReadAllText(Path.Combine(root, ".github", "workflows", "ci.yml"));
        var localGate = File.ReadAllText(Path.Combine(root, LocalHarnessGateScriptPath));
        var preflight = File.ReadAllText(Path.Combine(root, PreflightScriptPath));
        var sharedGate = File.ReadAllText(Path.Combine(root, ".github", "scripts", "harness-gate.sh"));
        var perfEvents = File.ReadAllText(Path.Combine(root, PerfEventScriptPath));
        var makefile = File.ReadAllText(Path.Combine(root, "Makefile"));

        Assert.Contains("make -C candidate dotnet", workflow, StringComparison.Ordinal);
        Assert.Contains("make -C candidate test-all", workflow, StringComparison.Ordinal);
        Assert.Contains("make -C candidate selftest", workflow, StringComparison.Ordinal);
        Assert.Contains("lean-report-pair.sh", localGate, StringComparison.Ordinal);
        Assert.Contains("--skip-engineering", localGate, StringComparison.Ordinal);
        Assert.Contains("GATE_ARGS=\"--skip-engineering\"", preflight, StringComparison.Ordinal);
        Assert.DoesNotContain("refactor-pr-a-required", localGate, StringComparison.Ordinal);
        Assert.Contains("gate_stage_timing", localGate, StringComparison.Ordinal);
        Assert.Contains("gate_timing_summary", localGate, StringComparison.Ordinal);
        Assert.Contains("STRATALINT_TIMING", sharedGate, StringComparison.Ordinal);
        Assert.Contains("gate_stage_timing", sharedGate, StringComparison.Ordinal);
        Assert.Contains("mark restore-judge", sharedGate, StringComparison.Ordinal);
        Assert.Contains("mark build-judge", sharedGate, StringComparison.Ordinal);
        Assert.DoesNotContain("PrAEffectiveness", makefile, StringComparison.Ordinal);
        Assert.DoesNotContain("STRATALINT_TIMING:-1", sharedGate, StringComparison.Ordinal);
        Assert.Contains("$JUDGE_ROOT/.github/scripts/harness-gate.sh", localGate, StringComparison.Ordinal);
        Assert.Contains("--candidate-lean-report", localGate, StringComparison.Ordinal);
        Assert.Contains("--baseline-lean-report", localGate, StringComparison.Ordinal);
        Assert.DoesNotContain("verify-conservative", sharedGate, StringComparison.Ordinal);
        Assert.Contains("STRATALINT_GATE_OUTCOME_DIR", sharedGate + preflight, StringComparison.Ordinal);
        Assert.Contains("gate-outcome-v1", sharedGate + preflight, StringComparison.Ordinal);
        Assert.DoesNotContain("make -C \"$CANDIDATE_ROOT\" dotnet", sharedGate, StringComparison.Ordinal);
        Assert.Contains("-getProperty:TargetPath", sharedGate, StringComparison.Ordinal);
        Assert.DoesNotContain("--baseline-harness", sharedGate, StringComparison.Ordinal);
        Assert.DoesNotContain("--candidate-harness", sharedGate, StringComparison.Ordinal);
        Assert.Contains(
            "exit_with_gate_outcome protected-surface-change 3",
            sharedGate,
            StringComparison.Ordinal);
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
        var root = FindRepositoryRoot();
        var preflight = File.ReadAllText(Path.Combine(root, PreflightScriptPath));

        var dotnetIndex = preflight.IndexOf("CI=true make dotnet", StringComparison.Ordinal);
        var leanReportIndex = preflight.IndexOf("make lean-report", StringComparison.Ordinal);
        var testIndex = preflight.IndexOf(
            "CI=true STRATALINT_REQUIRE_LIVE_REPORT=1 make test-all",
            StringComparison.Ordinal);

        Assert.True(dotnetIndex >= 0, "preflight must build the .NET report consumer");
        Assert.True(leanReportIndex >= 0, "preflight must refresh the raw Lean report");
        Assert.True(testIndex >= 0, "preflight must run the .NET tests");
        Assert.True(dotnetIndex < leanReportIndex, "the .NET build must precede report production");
        Assert.True(leanReportIndex < testIndex, "report production must precede every test consumer");
    }

    [Fact]
    public void PreflightPinsOneStrictAncestorBeforeExpensiveStagesAndReportsBaseAdvanceAdvisory()
    {
        var root = FindRepositoryRoot();
        var preflight = File.ReadAllText(Path.Combine(root, PreflightScriptPath));

        var fetchIndex = preflight.IndexOf("fetch --prune", StringComparison.Ordinal);
        var pinIndex = preflight.IndexOf(
            "BASE_SHA=\"$(git rev-parse --verify \"${BASE_REF}^{commit}\")\"",
            StringComparison.Ordinal);
        var ancestorIndex = preflight.IndexOf("merge-base --is-ancestor", StringComparison.Ordinal);
        var buildIndex = preflight.IndexOf("CI=true make dotnet", StringComparison.Ordinal);

        Assert.True(fetchIndex >= 0, "preflight must perform the run's single base fetch");
        Assert.True(pinIndex > fetchIndex, "the exact base OID must be resolved after the fetch");
        Assert.True(ancestorIndex > pinIndex, "the pinned OID must retain strict ancestor validation");
        Assert.True(buildIndex > ancestorIndex, "base validation must precede every expensive stage");
        Assert.Contains("make gate BASE=\"$BASE_SHA\"", preflight, StringComparison.Ordinal);
        Assert.Contains("BASE_ADVANCED pinned=%s observed=%s", preflight, StringComparison.Ordinal);
        Assert.Contains("|| true", preflight[preflight.IndexOf("BASE_ADVANCED", StringComparison.Ordinal)..], StringComparison.Ordinal);
    }

    [Fact]
    public void AdmissionBaselineCheckoutsRetainFrozenLedgerHistory()
    {
        var root = FindRepositoryRoot();
        var workflow = File.ReadAllText(Path.Combine(root, AdmissionWorkflowPath));
        const string baselineCheckout =
            "      - name: Check out content-addressed dev baseline\n";
        const string candidateCheckout = "      - name: Check out candidate with history\n";

        var baselineRegions = workflow.Split(baselineCheckout, StringSplitOptions.None);
        Assert.Equal(3, baselineRegions.Length);
        foreach (var region in baselineRegions.Skip(1))
        {
            var checkout = region[..region.IndexOf("      - name: ", StringComparison.Ordinal)];
            Assert.Contains("          fetch-depth: 0\n", checkout, StringComparison.Ordinal);
            Assert.DoesNotContain("          fetch-depth: 1\n", checkout, StringComparison.Ordinal);
        }

        var candidateRegions = workflow.Split(candidateCheckout, StringSplitOptions.None);
        Assert.Equal(3, candidateRegions.Length);
        foreach (var region in candidateRegions.Skip(1))
        {
            var checkout = region[..region.IndexOf("      - name: ", StringComparison.Ordinal)];
            Assert.Contains("          fetch-depth: 0\n", checkout, StringComparison.Ordinal);
        }
    }

    // 报告地址的 producer 分量取自**候选**树,而实际执行的 producer 取自**基线**树
    // (base-owned 判官拓扑要求如此)。push 事件下 baseline = github.event.before,
    // 即上一个 dev tip,故一次改动 lean-inspector 的合并会让两者不同:报告由旧 producer
    // 产出却按新 producer 的地址归档 —— 地址声称的输入闭包与实际闭包不符。
    // `verify` 只重算地址不重跑 producer,RawLeanReportArtifact 只核模块集与 source_sha256,
    // 二者都拦不住「同一份源、不同 producer 语义」。故缓存的读与写都必须带 producer 一致性守卫。
    [Fact]
    public void CanonicalLeanReportCacheIsGatedOnProducerIdentityOnBothReadAndWrite()
    {
        var admission = File.ReadAllText(Path.Combine(FindRepositoryRoot(), AdmissionWorkflowPath));

        var guarded = admission.Split('\n')
            .Where(static line => line.TrimStart().StartsWith("if:", StringComparison.Ordinal)
                && line.Contains("producer-consistent == 'true'", StringComparison.Ordinal))
            .ToArray();

        Assert.Equal(2, guarded.Length);
        Assert.Contains(
            guarded,
            static line => !line.Contains("refs/heads/dev", StringComparison.Ordinal));
        Assert.Contains(
            guarded,
            static line => line.Contains("refs/heads/dev", StringComparison.Ordinal));
        Assert.Contains(
            "echo \"producer-consistent=",
            admission,
            StringComparison.Ordinal);

        var reuseStep = admission.Split("      - name: Restore canonical Lean report by input address\n", StringSplitOptions.None)[1]
            .Split("      - name: ", StringSplitOptions.None)[0];
        Assert.Contains("pair-reusable == 'true'", reuseStep, StringComparison.Ordinal);
    }

    [Fact]
    public void TheoryIngestRestoresOrProducesBaseCanonicalReportInOneJob()
    {
        var root = FindRepositoryRoot();
        var admission = File.ReadAllText(Path.Combine(root, AdmissionWorkflowPath));
        var workflow = File.ReadAllText(Path.Combine(root, TheoryIngestWorkflowPath));
        var overlayIndex = workflow.IndexOf(
            "- name: Overlay judge harness onto candidate data",
            StringComparison.Ordinal);
        var addressIndex = workflow.IndexOf(
            "- name: Resolve base canonical Lean report address",
            StringComparison.Ordinal);
        var restoreIndex = workflow.IndexOf(
            "- name: Restore base canonical Lean report",
            StringComparison.Ordinal);
        var verifyIndex = workflow.IndexOf(
            "- name: Install and verify base canonical Lean report",
            StringComparison.Ordinal);
        var ingestIndex = workflow.IndexOf("          make ingest BASE=HEAD\n", StringComparison.Ordinal);

        Assert.True(overlayIndex >= 0, "theory ingest must overlay the base judge");
        Assert.True(addressIndex > overlayIndex, "report address must use the overlaid base judge");
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
            "- name: Produce base canonical Lean report on cache miss",
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
    }

    [Fact]
    public void TheoryIngestUsesSingleOverlaySourceForBaseClosureWithoutWriteback()
    {
        var root = FindRepositoryRoot();
        var workflow = File.ReadAllText(Path.Combine(root, TheoryIngestWorkflowPath));
        Assert.Contains("contents: read", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("Enforce candidate data-only boundary", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("Enforce write-path whitelist and commit back", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("theory-ingest-bot", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("THEORY-INGEST-REGISTRY-001", workflow, StringComparison.Ordinal);
        var ingestIndex = workflow.IndexOf("make ingest BASE=HEAD", StringComparison.Ordinal);
        var closureIndex = workflow.IndexOf(TheoryIngestClosureScriptPath, StringComparison.Ordinal);
        Assert.True(closureIndex > ingestIndex, "closure judge must run after ingest");
        Assert.Contains("$GITHUB_WORKSPACE/judge/" + TheoryIngestClosureScriptPath, workflow, StringComparison.Ordinal);

        const string overlaySource = "THEORY_INGEST_OVERLAY_PATHS";
        var overlayIndex = workflow.IndexOf(
            "      - name: Overlay judge harness onto candidate data",
            StringComparison.Ordinal);
        var overlayEndIndex = workflow.IndexOf(
            "      - name: ",
            overlayIndex + "      - name: ".Length,
            StringComparison.Ordinal);
        Assert.True(overlayIndex >= 0, "the judge overlay step must exist");
        Assert.True(overlayEndIndex > overlayIndex, "the judge overlay step must be bounded");

        var overlayStep = workflow[overlayIndex..overlayEndIndex];
        var closureStep = workflow[workflow.LastIndexOf(
            "      - name: Enforce theory ingest closure",
            StringComparison.Ordinal)..];
        Assert.Single(Regex.Matches(
            workflow,
            $@"(?m)^\s*{overlaySource}:\s*\|-\s*$",
            RegexOptions.CultureInvariant | RegexOptions.NonBacktracking));
        var overlayDeclaration = workflow[
            workflow.IndexOf($"      {overlaySource}: |-", StringComparison.Ordinal)..overlayIndex];
        Assert.Contains("Meta/StrataLint\n", overlayDeclaration, StringComparison.Ordinal);
        Assert.DoesNotContain("Meta/StrataLint/\n", overlayDeclaration, StringComparison.Ordinal);
        Assert.Equal(3, Regex.Matches(workflow, overlaySource).Count);
        Assert.Contains($"\"${overlaySource}\"", overlayStep, StringComparison.Ordinal);
        Assert.Contains($"\"${overlaySource}\"", closureStep, StringComparison.Ordinal);
        Assert.Contains("if [ -d \"$source\" ]", overlayStep, StringComparison.Ordinal);
        Assert.Contains("rsync -a --delete \"$source/\" \"$destination\"", overlayStep, StringComparison.Ordinal);
        Assert.Contains("cp \"$source\" \"$destination\"", overlayStep, StringComparison.Ordinal);
        Assert.Single(Regex.Matches(overlayStep, @"(?m)^\s*rsync\b"));
        Assert.Single(Regex.Matches(overlayStep, @"(?m)^\s*cp\b"));
        Assert.Contains("closure_args+=(--exclude \"$path\")", closureStep, StringComparison.Ordinal);
        Assert.DoesNotContain("${path%/}", closureStep, StringComparison.Ordinal);
        Assert.DoesNotMatch(
            new Regex(
                @"(?m)--exclude\s+[\""']?[A-Za-z0-9_.-]+(?:/[A-Za-z0-9_.-]+)*/?[\""']?(?:\s|\\|$)",
                RegexOptions.CultureInvariant | RegexOptions.NonBacktracking),
            closureStep);
    }

    [Fact]
    public void TheoryIngestNoLongerCarriesLegacyBoundaryOrWritebackContracts()
    {
        var root = FindRepositoryRoot();
        var workflow = File.ReadAllText(Path.Combine(root, TheoryIngestWorkflowPath));
        Assert.DoesNotContain("Enforce candidate data-only boundary", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("Enforce write-path whitelist and commit back", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("THEORY-INGEST-REGISTRY-001", workflow, StringComparison.Ordinal);
    }

    [Fact]
    public void TheoryIngestDoesNotRewriteEchoProjection()
    {
        var root = FindRepositoryRoot();
        var workflow = File.ReadAllText(Path.Combine(root, TheoryIngestWorkflowPath));
        Assert.DoesNotContain("Generated/echo-residuals", workflow, StringComparison.Ordinal);
    }

    [Fact]
    public void LocalGateHonorsExplicitTemporaryDirectory()
    {
        var root = FindRepositoryRoot();
        var localGate = File.ReadAllText(Path.Combine(root, LocalHarnessGateScriptPath));

        Assert.Contains(
            "mktemp -d \"${TMPDIR:-/tmp}/stratalint-local-gate.XXXXXXXX\"",
            localGate,
            StringComparison.Ordinal);
    }

    [Fact]
    public void ReportEntrypointsDelegateToTheSingleHostSupervisor()
    {
        var root = FindRepositoryRoot();
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
        var root = FindRepositoryRoot();
        var script = File.ReadAllText(Path.Combine(root, ScribeScriptPath));

        Assert.DoesNotContain("lean-inspector/inspect.sh", script, StringComparison.Ordinal);
        Assert.DoesNotContain("SCRIBE_USE_EXISTING_REPORT", script, StringComparison.Ordinal);
        Assert.Contains(ReportConsumerScriptPath, script, StringComparison.Ordinal);
        Assert.Contains("scribe-consumer", script, StringComparison.Ordinal);
        Assert.Contains(".lake/build/stratalint/raw-lean-report.json", script, StringComparison.Ordinal);
        Assert.DoesNotContain("CHECK_ARGS=()", script, StringComparison.Ordinal);
        Assert.Contains("emit|emit-values|filemap) run_scribe \"$1\"", script, StringComparison.Ordinal);
        Assert.Contains("emit|check)", script, StringComparison.Ordinal);
        Assert.Contains("usage: scribe.sh emit|check", script, StringComparison.Ordinal);
        Assert.Contains("canonical) generators=(emit emit-values filemap dag)", script, StringComparison.Ordinal);
        Assert.Contains("for generator in \"${generators[@]}\"", script, StringComparison.Ordinal);
    }

    [Fact]
    public void WorktreeAdapterRestoresToolPathBeforeResolvingRepositoryRoot()
    {
        var root = FindRepositoryRoot();
        var script = File.ReadAllText(Path.Combine(root, WorktreeInitScriptPath));
        var pathIndex = script.IndexOf("export PATH=", StringComparison.Ordinal);
        var dirnameIndex = script.IndexOf("dirname", StringComparison.Ordinal);

        Assert.True(pathIndex >= 0, "worktree adapter must restore the process tool path");
        Assert.True(pathIndex < dirnameIndex, "tool PATH must be restored before dirname is invoked");
    }

    [Fact]
    public void PerformanceJsonQuoteRemovesUnsupportedControlBytes()
    {
        var root = FindRepositoryRoot();
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
        var root = FindRepositoryRoot();
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

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "CLAUDE.md"))) return current.FullName;
        }

        throw new DirectoryNotFoundException("Could not locate repository root.");
    }
}
