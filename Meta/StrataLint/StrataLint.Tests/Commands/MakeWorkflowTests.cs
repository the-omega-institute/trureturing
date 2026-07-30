using System.Text.RegularExpressions;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class MakeWorkflowTests
{
    private const string DotnetBuildScriptPath = "Meta/StrataLint/scripts/dotnet-build.sh";
    private const string FkstRunScriptPath = ".fkst/scripts/run.sh";
    private const string ScribeScriptPath = "Meta/StrataLint/scripts/scribe.sh";
    private const string SelftestScriptPath = "Meta/StrataLint/scripts/stratalint-selftest.sh";
    private const string LocalHarnessGateScriptPath =
        "Meta/StrataLint/scripts/local-harness-gate.sh";
    private const string PreflightScriptPath = "Meta/StrataLint/scripts/preflight.sh";
    private const string CleanLanesScriptPath = "Meta/StrataLint/scripts/clean-lanes.sh";
    private const string WorktreeInitScriptPath = "Meta/StrataLint/scripts/worktree-init.sh";
    private const string LeanReportScriptPath =
        "Meta/StrataLint/scripts/report/lean-report.sh";
    private const string IngestScriptPath = "Meta/StrataLint/scripts/ingest.sh";
    private const string EchoResidualSummaryScriptPath =
        "Meta/StrataLint/scripts/report/echo-residual-summary.sh";
    private const string EchoVerifyScriptPath =
        "Meta/StrataLint/scripts/report/echo-verify.sh";
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
    private const string EchoResidualSummaryPath = "Generated/echo-residual-summary.md";
    private const string PrShepherdScriptPath = "Meta/StrataLint/scripts/pr-shepherd.sh";

    private static readonly string[] Targets =
    [
        "help",
        "dotnet",
        "test",
        "lua-test",
        "lean",
        "lean-report",
        "build",
        "c0-renew",
        "clean-lanes",
        "emit",
        "emit-check",
        "ingest",
        "echo-residual-summary",
        "echo-verify",
        "record-golden",
        "selftest",
        "scratch-sweep",
        "gate",
        "perf-report",
        "worktree",
    ];

    [Fact]
    public void MakefileIsAThinCompleteDispatchTable()
    {
        var root = FindRepositoryRoot();
        var makefile = File.ReadAllText(Path.Combine(root, "Makefile"));

        Assert.Contains(".DEFAULT_GOAL := help", makefile, StringComparison.Ordinal);
        var phony = Assert.Single(
            makefile.Split('\n'),
            static line => line.StartsWith(".PHONY:", StringComparison.Ordinal));
        Assert.Equal(Targets, phony[".PHONY:".Length..].Split(' ', StringSplitOptions.RemoveEmptyEntries));
        foreach (var target in Targets)
        {
            Assert.Matches(new Regex($"(?m)^{Regex.Escape(target)}:", RegexOptions.CultureInvariant), makefile);
            Assert.InRange(RecipeCount(makefile, target), 0, 1);
        }

        Assert.Contains("build: dotnet lean", makefile, StringComparison.Ordinal);
        Assert.Equal(0, RecipeCount(makefile, "build"));
        Assert.Contains(
            " c0-renew --base \"$(BASE)\"",
            Recipe(makefile, "c0-renew"),
            StringComparison.Ordinal);
        Assert.Contains(CleanLanesScriptPath, Recipe(makefile, "clean-lanes"), StringComparison.Ordinal);
        Assert.Contains(DotnetBuildScriptPath, Recipe(makefile, "dotnet"), StringComparison.Ordinal);
        Assert.Contains("dotnet test", Recipe(makefile, "test"), StringComparison.Ordinal);
        Assert.Contains(FkstRunScriptPath + " test", Recipe(makefile, "lua-test"), StringComparison.Ordinal);
        Assert.Contains("lake build", Recipe(makefile, "lean"), StringComparison.Ordinal);
        Assert.Contains(LeanReportScriptPath, Recipe(makefile, "lean-report"), StringComparison.Ordinal);
        Assert.Contains(ScribeScriptPath + " emit", Recipe(makefile, "emit"), StringComparison.Ordinal);
        Assert.Contains("emit-check: echo-verify", makefile, StringComparison.Ordinal);
        Assert.Contains(ScribeScriptPath + " check", Recipe(makefile, "emit-check"), StringComparison.Ordinal);
        Assert.DoesNotContain("ingest: emit-check", makefile, StringComparison.Ordinal);
        Assert.Contains(IngestScriptPath, Recipe(makefile, "ingest"), StringComparison.Ordinal);
        Assert.Contains(
            EchoResidualSummaryScriptPath,
            Recipe(makefile, "echo-residual-summary"),
            StringComparison.Ordinal);
        Assert.Contains(EchoVerifyScriptPath, Recipe(makefile, "echo-verify"), StringComparison.Ordinal);
        Assert.Contains("golden-record", Recipe(makefile, "record-golden"), StringComparison.Ordinal);
        Assert.Contains(SelftestScriptPath, Recipe(makefile, "selftest"), StringComparison.Ordinal);
        Assert.Contains("stratalint-c0-renew-", Recipe(makefile, "scratch-sweep"), StringComparison.Ordinal);
        Assert.Contains(LocalHarnessGateScriptPath, Recipe(makefile, "gate"), StringComparison.Ordinal);
        Assert.Contains(PerfReportScriptPath, Recipe(makefile, "perf-report"), StringComparison.Ordinal);
        Assert.Contains("Golden/perf-budgets.toml", Recipe(makefile, "perf-report"), StringComparison.Ordinal);
        Assert.Contains(WorktreeInitScriptPath, Recipe(makefile, "worktree"), StringComparison.Ordinal);
    }

    [Fact]
    public void HelpRunsAndNamesEveryTarget()
    {
        var root = FindRepositoryRoot();
        var result = BoundedProcessRunner.Run(
            "make",
            ["help"],
            root,
            TimeSpan.FromSeconds(30),
            64 * 1024);

        Assert.Equal(0, result.ExitCode);
        var output = System.Text.Encoding.UTF8.GetString(result.StandardOutput);
        Assert.All(Targets, target => Assert.Contains($"make {target}", output, StringComparison.Ordinal));
        Assert.Contains("dry-run", output, StringComparison.Ordinal);
        Assert.Contains("FORCE=1", output, StringComparison.Ordinal);
        Assert.Contains("values", output, StringComparison.OrdinalIgnoreCase);
    }

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
            printf '%s\n' '<!-- echo-residual-summary:v2 base=git-sha1:2222222222222222222222222222222222222222 -->' '# Echo Residual Summary' '<!-- /echo-residual-summary:v2 -->'
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
            <!-- echo-residual-summary:v2 base=git-sha1:2222222222222222222222222222222222222222 -->
            # Echo Residual Summary
            <!-- /echo-residual-summary:v2 -->
            """ + "\n",
            System.Text.Encoding.UTF8.GetString(result.StandardOutput));
        Assert.Equal("lean provenance\n", System.Text.Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void EchoVerifyMakeDefaultsToTheCommittedProjection()
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
            Path.Combine(root, EchoVerifyScriptPath),
            Path.Combine(fixture.Path, EchoVerifyScriptPath));
        File.WriteAllText(
            Path.Combine(binDirectory, "dotnet"),
            """
            #!/usr/bin/env bash
            [[ "$*" == *"echo-verify --base synthetic-base --if-affected"* ]] || exit 19
            [[ "$*" != *"--file"* ]] || exit 20
            printf 'ECHO_VERIFY_OK\n'
            """);
        File.SetUnixFileMode(
            Path.Combine(binDirectory, "dotnet"),
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);

        var result = BoundedProcessRunner.Run(
            "/bin/bash",
            ["-c", "PATH=\"$1:$PATH\" exec make --no-print-directory echo-verify BASE=synthetic-base", "echo-make", binDirectory],
            fixture.Path,
            TimeSpan.FromSeconds(30),
            64 * 1024);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal("ECHO_VERIFY_OK\n", System.Text.Encoding.UTF8.GetString(result.StandardOutput));
        Assert.Empty(result.StandardError);
    }

    [Fact]
    public void EmitCheckRunsEchoVerifierAndScribeCheckAgainstTheSameBase()
    {
        if (OperatingSystem.IsWindows()) return;

        var root = FindRepositoryRoot();
        using var fixture = new TemporaryDirectory();
        var scriptsDirectory = Path.Combine(fixture.Path, "Meta", "StrataLint", "scripts");
        var reportDirectory = Path.Combine(scriptsDirectory, "report");
        Directory.CreateDirectory(reportDirectory);
        File.Copy(Path.Combine(root, "Makefile"), Path.Combine(fixture.Path, "Makefile"));
        File.WriteAllText(
            Path.Combine(fixture.Path, ScribeScriptPath),
            "#!/usr/bin/env bash\n[[ \"$1\" == check ]] || exit 18\nprintf 'SCRIBE_CHECK\\n'\n");
        File.WriteAllText(
            Path.Combine(fixture.Path, EchoVerifyScriptPath),
            "#!/usr/bin/env bash\n[[ \"$1\" == \"\" ]] || exit 19\n[[ \"$2\" == synthetic-base ]] || exit 20\nprintf 'ECHO_VERIFY\\n'\n");

        var result = BoundedProcessRunner.Run(
            "make",
            ["--no-print-directory", "emit-check", "BASE=synthetic-base"],
            fixture.Path,
            TimeSpan.FromSeconds(30),
            64 * 1024);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(
            "ECHO_VERIFY\nSCRIBE_CHECK\n",
            System.Text.Encoding.UTF8.GetString(result.StandardOutput));
        Assert.Empty(result.StandardError);
    }

    [Fact]
    public void PreflightAndRequiredBaselineGateDelegateToEchoVerify()
    {
        var root = FindRepositoryRoot();
        var workflow = File.ReadAllText(Path.Combine(root, ".github", "workflows", "ci.yml"));
        var localGate = File.ReadAllText(Path.Combine(root, LocalHarnessGateScriptPath));
        var sharedGate = File.ReadAllText(Path.Combine(root, ".github", "scripts", "harness-gate.sh"));
        var preflight = File.ReadAllText(Path.Combine(root, PreflightScriptPath));

        Assert.Contains("types: [opened, synchronize, reopened]", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("github.event.pull_request.body", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("--echo-review", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("--echo-review", sharedGate, StringComparison.Ordinal);
        Assert.Contains("dotnet \"$JUDGE_DLL\" echo-verify", sharedGate, StringComparison.Ordinal);
        Assert.Contains("--if-affected", sharedGate, StringComparison.Ordinal);
        Assert.Contains("echo-verify-bootstrap", localGate, StringComparison.Ordinal);
        Assert.Contains("make -C \"$CANDIDATE_ROOT\" echo-verify", localGate, StringComparison.Ordinal);
        Assert.DoesNotContain("make echo-verify", preflight, StringComparison.Ordinal);
    }

    [Fact]
    public void EchoProjectionIsARegisteredGeneratedArtifactNotFlightScaffolding()
    {
        var root = FindRepositoryRoot();
        var registry = File.ReadAllText(Path.Combine(root, "Meta", "registry.yaml"));
        var fileMap = File.ReadAllText(Path.Combine(root, "Meta", "FILEMAP.toml"));
        var gitignore = File.ReadAllText(Path.Combine(root, ".gitignore"));

        Assert.Contains($"  - \"{EchoResidualBlock.RelativePath}\"", registry, StringComparison.Ordinal);
        Assert.Contains($"pattern = \"{EchoResidualBlock.RelativePath}\"", fileMap, StringComparison.Ordinal);
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

        Assert.Contains("make -C candidate dotnet", workflow, StringComparison.Ordinal);
        Assert.Contains("make -C candidate test", workflow, StringComparison.Ordinal);
        Assert.Contains("make -C candidate lua-test", workflow, StringComparison.Ordinal);
        Assert.Contains("make -C candidate selftest", workflow, StringComparison.Ordinal);
        Assert.Contains("make lua-test", preflight, StringComparison.Ordinal);
        Assert.Contains("make -C \"$CANDIDATE_ROOT\" emit-check", localGate, StringComparison.Ordinal);
        Assert.Contains("emit-check BASE=\"$BASE_SHA\"", localGate, StringComparison.Ordinal);
        Assert.Contains("lean-report-pair.sh", localGate, StringComparison.Ordinal);
        Assert.Contains("--skip-engineering", localGate, StringComparison.Ordinal);
        Assert.Contains("GATE_ARGS=--skip-engineering", preflight, StringComparison.Ordinal);
        Assert.Contains("gate_stage_timing", localGate, StringComparison.Ordinal);
        Assert.Contains("gate_timing_summary", localGate, StringComparison.Ordinal);
        Assert.Contains("STRATALINT_TIMING", sharedGate, StringComparison.Ordinal);
        Assert.Contains("gate_stage_timing", sharedGate, StringComparison.Ordinal);
        Assert.DoesNotContain("STRATALINT_TIMING:-1", sharedGate, StringComparison.Ordinal);
        Assert.Contains("$JUDGE_ROOT/.github/scripts/harness-gate.sh", localGate, StringComparison.Ordinal);
        Assert.Contains("--candidate-lean-report", localGate, StringComparison.Ordinal);
        Assert.Contains("--baseline-lean-report", localGate, StringComparison.Ordinal);
        Assert.Contains("verify-conservative", sharedGate, StringComparison.Ordinal);
        Assert.Contains("make -C \"$CANDIDATE_ROOT\" dotnet", sharedGate, StringComparison.Ordinal);
        Assert.Contains("-getProperty:TargetPath", sharedGate, StringComparison.Ordinal);
        Assert.Contains("--baseline-harness", sharedGate, StringComparison.Ordinal);
        Assert.Contains("--candidate-harness", sharedGate, StringComparison.Ordinal);
        Assert.Contains("exit 3", sharedGate, StringComparison.Ordinal);
        Assert.DoesNotContain("Bootstrap scaffold path", sharedGate, StringComparison.Ordinal);
        Assert.Contains("gate_rc", localGate, StringComparison.Ordinal);
        Assert.Contains("$gate_rc -eq 3", localGate, StringComparison.Ordinal);
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

    [Fact]
    public void TheoryIngestRestoresBaseCanonicalReportWithoutCandidateLeanBuild()
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
        var admissionCacheKey = Assert.Single(
            admission.Split('\n'),
            static line => line.TrimStart().StartsWith(
                "key: stratalint-canonical-lean-report-v1-",
                StringComparison.Ordinal));
        var ingestCacheKey = Assert.Single(
            workflow.Split('\n')
                .Where(static line => line.TrimStart().StartsWith(
                    "key: stratalint-canonical-lean-report-v1-",
                    StringComparison.Ordinal))
                .Select(static line => line.Trim())
                .Distinct());
        Assert.Equal(admissionCacheKey.Trim(), ingestCacheKey);

        // 竞态防护契约:缓存由 ci.yml 并行生产,ingest 须以 lookup-only 探测 + 无凭据
        // 等待重试盖住生产窗口;最终 restore 保持 fail-closed,等待不降级检测。
        var probeIndex = workflow.IndexOf(
            "- name: Probe base canonical Lean report cache",
            StringComparison.Ordinal);
        var reprobeIndex = workflow.IndexOf(
            "- name: Re-probe base canonical Lean report cache",
            StringComparison.Ordinal);
        var finalRestoreIndex = workflow.IndexOf(
            "- name: Restore base canonical Lean report",
            StringComparison.Ordinal);
        Assert.True(probeIndex >= 0, "cache production race must be probed before restore");
        Assert.True(reprobeIndex > probeIndex, "the probe must retry across the production window");
        Assert.True(finalRestoreIndex > reprobeIndex, "the fail-closed restore must come after all probes");
        Assert.Contains("lookup-only: true", workflow[probeIndex..finalRestoreIndex], StringComparison.Ordinal);
        Assert.Contains("fail-on-cache-miss: true", workflow[finalRestoreIndex..], StringComparison.Ordinal);

        // 等待方向契约:等待/重探必须挂在"未命中"上(cache-hit 在 miss 时为空串,
        // 故唯一正确谓词是 != 'true');挂反(== 'true')会使正常路径空等、竞态路径
        // 直接失败——修复整体失效。
        var waitRegion = workflow[probeIndex..finalRestoreIndex];
        Assert.Contains("outputs.cache-hit != 'true'", waitRegion, StringComparison.Ordinal);
        Assert.DoesNotContain("outputs.cache-hit == 'true'", waitRegion, StringComparison.Ordinal);

        // 等待实体契约(对抗评审实证:sleep 拔成 0 曾不亮红):两次等待必须真实存在
        // 且量级足以盖住约 10 分钟的生产窗口——锁"芯"而不只锁"壳"。
        Assert.Equal(
            2,
            Regex.Matches(waitRegion, Regex.Escape("run: sleep 360")).Count);
        Assert.Contains("steps.lean-report-input.outputs.address", admissionCacheKey, StringComparison.Ordinal);
        Assert.Contains(
            "$(basename \"$target\")\" > \"${target}.sha256\"",
            admission,
            StringComparison.Ordinal);
        Assert.Contains("steps.lean-report-cache.outputs.cache-hit", workflow, StringComparison.Ordinal);
        Assert.Contains(LeanReportInputScriptPath, workflow, StringComparison.Ordinal);
        Assert.Contains("\" verify \\", workflow, StringComparison.Ordinal);
        Assert.Contains(".lake/build/stratalint/raw-lean-report.json", workflow, StringComparison.Ordinal);
        Assert.Contains("timeout-minutes: 30", workflow, StringComparison.Ordinal);
        Assert.Contains("actions: read", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("          make lean\n", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("          make lean-report\n", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("Install pinned Lean toolchain", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("Restore candidate Lean build artifacts", workflow, StringComparison.Ordinal);
        Assert.DoesNotContain("uses: actions/cache@v4", workflow, StringComparison.Ordinal);
    }

    [Fact]
    public void TheoryIngestKeepsCandidateExecutionCredentiallessAndDataOnly()
    {
        var root = FindRepositoryRoot();
        var workflow = File.ReadAllText(Path.Combine(root, TheoryIngestWorkflowPath));
        var candidateCheckoutIndex = workflow.IndexOf(
            "- name: Check out PR head (data + commit target)",
            StringComparison.Ordinal);
        var boundaryIndex = workflow.IndexOf(
            "- name: Enforce candidate data-only boundary",
            StringComparison.Ordinal);
        var reportRestoreIndex = workflow.IndexOf(
            "- name: Restore base canonical Lean report",
            StringComparison.Ordinal);
        var commitIndex = workflow.IndexOf(
            "- name: Enforce write-path whitelist and commit back",
            StringComparison.Ordinal);

        Assert.True(candidateCheckoutIndex >= 0, "candidate checkout must be explicit");
        Assert.True(boundaryIndex > candidateCheckoutIndex, "the data boundary must follow checkout");
        Assert.True(
            reportRestoreIndex > boundaryIndex,
            "candidate inputs must be classified before the report is restored");
        Assert.True(
            commitIndex > reportRestoreIndex,
            "write credentials must only appear after candidate report consumption");

        var candidateCheckout = workflow[candidateCheckoutIndex..boundaryIndex];
        Assert.Contains(
            "ref: ${{ github.event.pull_request.head.sha }}",
            candidateCheckout,
            StringComparison.Ordinal);
        Assert.Contains("persist-credentials: false", candidateCheckout, StringComparison.Ordinal);

        var boundary = workflow[boundaryIndex..reportRestoreIndex];
        var theoryDataPattern = string.Concat("docs/develop/", "theory/*");
        Assert.Contains("BASE_SHA: ${{ github.event.pull_request.base.sha }}", boundary, StringComparison.Ordinal);
        Assert.Contains("HEAD_SHA: ${{ github.event.pull_request.head.sha }}", boundary, StringComparison.Ordinal);
        Assert.Contains(
            theoryDataPattern
                + "|Meta/BACKFILL.yaml|Meta/Digestion/atoms/*|"
                + EchoResidualSummaryPath,
            boundary,
            StringComparison.Ordinal);
        Assert.Contains("diff --name-only --no-renames -z", boundary, StringComparison.Ordinal);

        var reportInstallIndex = workflow.IndexOf(
            "- name: Install and verify base canonical Lean report",
            StringComparison.Ordinal);
        var cache = workflow[reportRestoreIndex..reportInstallIndex];
        Assert.DoesNotContain("restore-keys:", cache, StringComparison.Ordinal);
        Assert.DoesNotContain("GH_TOKEN:", workflow[..commitIndex], StringComparison.Ordinal);

        var commit = workflow[commitIndex..];
        Assert.Contains("GH_TOKEN: ${{ github.token }}", commit, StringComparison.Ordinal);
        Assert.Contains("gh auth setup-git", commit, StringComparison.Ordinal);
        var restoreOverlayIndex = commit.IndexOf(
            "git restore --source=HEAD -- Meta/StrataLint Makefile global.json",
            StringComparison.Ordinal);
        var cleanOverlayIndex = commit.IndexOf(
            "git clean -fd -- Meta/StrataLint",
            StringComparison.Ordinal);
        var inspectChangesIndex = commit.IndexOf(
            "changed=\"$(git status --porcelain)\"",
            StringComparison.Ordinal);
        Assert.True(restoreOverlayIndex >= 0, "tracked judge overlay files must be restored");
        Assert.True(cleanOverlayIndex > restoreOverlayIndex, "untracked judge overlay files must be removed");
        Assert.True(inspectChangesIndex > cleanOverlayIndex, "the whitelist must inspect the cleaned candidate");
    }

    [Fact]
    public void TheoryIngestReemitsBaseBoundEchoProjectionBeforeWriteback()
    {
        var root = FindRepositoryRoot();
        var workflow = File.ReadAllText(Path.Combine(root, TheoryIngestWorkflowPath));
        var ingestIndex = workflow.IndexOf("          make ingest BASE=HEAD\n", StringComparison.Ordinal);
        var emitIndex = workflow.IndexOf(
            "- name: Re-emit base-bound echo projection",
            StringComparison.Ordinal);
        var commitIndex = workflow.IndexOf(
            "- name: Enforce write-path whitelist and commit back",
            StringComparison.Ordinal);

        Assert.True(ingestIndex >= 0, "theory ingest must update the digestion ledger first");
        Assert.True(emitIndex > ingestIndex, "echo projection must be derived from the updated ledger");
        Assert.True(commitIndex > emitIndex, "echo projection must be emitted before writeback");

        var emission = workflow[emitIndex..commitIndex];
        Assert.Contains(
            "BASE_SHA: ${{ github.event.pull_request.base.sha }}",
            emission,
            StringComparison.Ordinal);
        Assert.Contains("echo-verify --emit --base \"$BASE_SHA\"", emission, StringComparison.Ordinal);
        Assert.Contains("> \"$projection\"", emission, StringComparison.Ordinal);
        Assert.Contains($"mv \"$projection\" {EchoResidualSummaryPath}", emission, StringComparison.Ordinal);
        Assert.DoesNotContain("make echo-residual-summary", emission, StringComparison.Ordinal);
        Assert.DoesNotContain("echo-verify --emit --base HEAD", emission, StringComparison.Ordinal);

        var commit = workflow[commitIndex..];
        Assert.Contains(EchoResidualSummaryPath, commit, StringComparison.Ordinal);
        Assert.Contains($"git add Meta/BACKFILL.yaml Meta/Digestion/atoms {EchoResidualSummaryPath}", commit, StringComparison.Ordinal);
    }

    [Fact]
    public void LocalGateHonorsExplicitTemporaryDirectory()
    {
        var root = FindRepositoryRoot();
        var localGate = File.ReadAllText(Path.Combine(root, LocalHarnessGateScriptPath));

        Assert.Contains("LOCAL_GATE_TMP_ROOT=\"${TMPDIR:-}\"", localGate, StringComparison.Ordinal);
        Assert.Contains(
            "if [[ -z \"$LOCAL_GATE_TMP_ROOT\" && -d /private/tmp ]]; then LOCAL_GATE_TMP_ROOT=/private/tmp; fi",
            localGate,
            StringComparison.Ordinal);
        Assert.Contains(
            "if [[ -z \"$LOCAL_GATE_TMP_ROOT\" ]]; then LOCAL_GATE_TMP_ROOT=/tmp; fi",
            localGate,
            StringComparison.Ordinal);
        Assert.Contains(
            "mktemp -d \"$LOCAL_GATE_TMP_ROOT/stratalint-local-gate.XXXXXXXX\"",
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
        Assert.Contains("run_scribe emit", script, StringComparison.Ordinal);
        Assert.Contains("run_scribe catalog", script, StringComparison.Ordinal);
        Assert.Contains("run_scribe emit-values", script, StringComparison.Ordinal);
        Assert.Contains("run_scribe filemap", script, StringComparison.Ordinal);
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

    [Fact]
    public void PrShepherdWakesArmedPrsWhoseHeadHasNoChecks()
    {
        var root = FindRepositoryRoot();
        var shepherd = File.ReadAllText(Path.Combine(root, PrShepherdScriptPath));

        // 采集面:sweep 必须读到 head 与 checks 数,否则判不出"armed 但 head 无 checks"
        // 的死锁类(bot 以 GITHUB_TOKEN push 不触发 workflow 的防递归缺口)。
        Assert.Contains("statusCheckRollup", shepherd, StringComparison.Ordinal);
        Assert.Contains("headRefOid", shepherd, StringComparison.Ordinal);

        // 防误触:同一 head 连续两轮观察无 checks 才唤醒(checks 挂载有延迟)。
        Assert.Contains("nochecks-", shepherd, StringComparison.Ordinal);

        // 唤醒动作:本地身份 close→reopen 重铸触发事件;close 会撤 auto-merge,
        // 唤醒后必须重挂,否则绿灯也不合。
        var wakeIndex = shepherd.IndexOf("wake_pr()", StringComparison.Ordinal);
        Assert.True(wakeIndex >= 0, "the shepherd must define a wake action for checkless armed PRs");
        var wake = shepherd[wakeIndex..];
        var closeIndex = wake.IndexOf("pr close", StringComparison.Ordinal);
        var reopenIndex = wake.IndexOf("pr reopen", StringComparison.Ordinal);
        var rearmIndex = wake.IndexOf("--auto --merge", StringComparison.Ordinal);
        Assert.True(closeIndex >= 0, "wake must close the PR to mint a fresh trigger event");
        Assert.True(reopenIndex > closeIndex, "wake must reopen after close");
        Assert.True(rearmIndex > reopenIndex, "close disarms auto-merge; wake must re-arm it");
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
