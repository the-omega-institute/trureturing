using System.Text.RegularExpressions;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class MakeWorkflowTests
{
    private const string ScribeScriptPath = "tools/scripts/scribe.sh";
    private const string LocalHarnessGateScriptPath =
        "tools/scripts/local-harness-gate.sh";
    private const string PreflightScriptPath = "tools/scripts/preflight.sh";
    private const string AdmissionBaseScriptPath =
        "tools/scripts/lib/admission-base-lib.sh";
    private const string ScribeContentChecksScriptPath =
        "tools/scripts/workflow/scribe-content-checks.sh";
    private const string InstallLeanToolchainScriptPath =
        "tools/scripts/workflow/install-lean-toolchain.sh";
    private const string WorktreeInitScriptPath = "tools/scripts/worktree-init.sh";
    private const string CleanLanesScriptPath = "tools/scripts/clean-lanes.sh";
    private const string LeanReportScriptPath =
        "tools/scripts/report/lean-report.sh";
    private const string LeanCacheEnsureScriptPath =
        "tools/scripts/worktree/lean-cache-ensure.sh";
    private const string LeanCacheRunScriptPath =
        "tools/scripts/worktree/lean-cache-run.sh";
    private const string WarmDonorScriptPath =
        "tools/scripts/worktree/warm-donor.sh";
    private const string IngestScriptPath = "tools/scripts/ingest.sh";
    private const string EchoResidualSummaryScriptPath =
        "tools/scripts/report/echo-residual-summary.sh";
    private const string ReportConsumerScriptPath =
        "tools/scripts/report/report-consumer.sh";
    private const string ReportSupervisorScriptPath =
        "tools/scripts/report/report-supervisor.sh";
    private const string LeanReportInputScriptPath =
        "tools/scripts/report/lean-report-input.sh";
    private const string LeanReportPairScriptPath = "tools/scripts/lean-report-pair.sh";
    private const string RendererContractUpdateScriptPath =
        "tools/scripts/update-renderer-contract.sh";
    private const string ToolsMakefilePath = "tools/Makefile";
    private const string AdmissionWorkflowPath = ".github/workflows/ci.yml";
    private const string PrOpenScriptPath = "tools/scripts/pr.sh open";
    private const string PrWatchScriptPath = "tools/scripts/pr.sh watch";

    private static readonly string[] RootTargets =
    [
        "help",
        "test",
        "lean-cache-ensure",
        "lean-cache-to-github-without-mathlib",
        "lean-cache-from-github-without-mathlib",
        "warm-donor",
        "lean",
        "lean-report",
        "build",
        "emit",
        "ingest",
        "align-digestion-status",
        "echo-residual-summary",
        "show-atom",
        "theory-candidates",
        "truth-export",
        "deliver-check",
        "receipts-stage",
        "deposit",
        "cover",
        "cover-batch",
        "worktree",
        "worktree-clean",
        "pr-open",
        "pr-watch",
        "preflight",
        "gate",
    ];

    private static readonly string[] ToolsTargets =
    [
        "help",
        "dotnet",
        "test",
        "engineering-tests",
        "selftest",
        "update-renderer-contract",
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

        var result = TestProcessRunner.Run(
            "/bin/bash",
            ["-c", "PATH=\"$1:$PATH\" exec make --no-print-directory echo-residual-summary BASE=synthetic-base", "echo-make", binDirectory],
            fixture.Path,
            BoundedProcessRunner.HangDetectionBudget,
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
    public void TheoryCandidatesOwnerOverrideFilePreservesBytesAcrossMakeBoundary()
    {
        if (OperatingSystem.IsWindows()) return;

        var root = TestRepositoryLayout.FindRoot();
        using var fixture = new TemporaryDirectory();
        var binDirectory = Path.Combine(fixture.Path, "bin");
        var cliDirectory = Path.Combine(fixture.Path, "tools", "StrataLint.Cli");
        Directory.CreateDirectory(binDirectory);
        Directory.CreateDirectory(cliDirectory);
        File.Copy(Path.Combine(root, "Makefile"), Path.Combine(fixture.Path, "Makefile"));
        var problemBytes = System.Text.Encoding.UTF8.GetBytes(
            "Does \"x\" imply $HOME and `id`?\nClassify ξ exactly.\n");
        var problemPath = Path.Combine(fixture.Path, "owner-problem.txt");
        File.WriteAllBytes(problemPath, problemBytes);
        var dotnetPath = Path.Combine(binDirectory, "dotnet");
        File.WriteAllText(
            dotnetPath,
            """
            #!/usr/bin/env bash
            while [[ $# -gt 0 ]]; do
              if [[ "$1" == "--owner-override-file" && $# -ge 2 ]]; then
                /bin/cat -- "$2"
                exit 0
              fi
              shift
            done
            exit 21
            """ + "\n");
        File.SetUnixFileMode(
            dotnetPath,
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);

        var result = TestProcessRunner.Run(
            "/bin/bash",
            [
                "-c",
                "PATH=\"$1:$PATH\" exec make --no-print-directory theory-candidates OWNER_OVERRIDE_FILE=\"$2\"",
                "theory-candidates-make",
                binDirectory,
                problemPath,
            ],
            fixture.Path,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(problemBytes, result.StandardOutput);
        Assert.Empty(result.StandardError);
    }


    [Fact]
    public void CiAndLocalGateReuseCanonicalEntrypoints()
    {
        var root = TestRepositoryLayout.FindRoot();
        var workflow = File.ReadAllText(Path.Combine(root, ".github", "workflows", "ci.yml"));
        var localGate = File.ReadAllText(Path.Combine(root, LocalHarnessGateScriptPath));
        var preflight = File.ReadAllText(Path.Combine(root, PreflightScriptPath));
        var sharedGate = File.ReadAllText(Path.Combine(root, ".github", "scripts", "harness-gate.sh"));
        var makefile = File.ReadAllText(Path.Combine(root, "Makefile"));

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
    public void PreflightRefreshesLeanReportAfterDotnetAndBeforeTests()
    {
        var root = TestRepositoryLayout.FindRoot();
        var preflight = File.ReadAllText(Path.Combine(root, PreflightScriptPath));

        var dotnetIndex = preflight.IndexOf("CI=true make -C tools dotnet", StringComparison.Ordinal);
        var leanReportIndex = preflight.IndexOf("make lean-report", StringComparison.Ordinal);
        var testIndex = preflight.IndexOf(
            "CI=true STRATALINT_REQUIRE_LIVE_REPORT=1 make -C tools engineering-tests",
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
        Assert.Contains(".materials.zip", consumer, StringComparison.Ordinal);
        Assert.DoesNotContain("may be stale", consumer, StringComparison.Ordinal);
    }

    [Fact]
    public void IngestWrapperSeparatesReportFreeDigestionFromTruthAlignment()
    {
        var script = File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/ingest.sh"));

        Assert.Contains("lean-report-input.sh", script, StringComparison.Ordinal);
        Assert.Contains(" address --repository ", script, StringComparison.Ordinal);
        Assert.Contains("git -C \"$ROOT\" archive", script, StringComparison.Ordinal);
        Assert.DoesNotContain(
            "input_state=\"$(report_input_state)\"",
            script,
            StringComparison.Ordinal);
        Assert.Contains("report_input_state\n    cleanup", script, StringComparison.Ordinal);
        Assert.Contains(
            "ingest --base \"$BASE\" --report-input-state \"$REPORT_INPUT_STATE\"",
            script,
            StringComparison.Ordinal);
        Assert.Contains("align-digestion-status)", script, StringComparison.Ordinal);
        Assert.Contains(
            "--role digestion-alignment-consumer --report \"$REPORT\"",
            script,
            StringComparison.Ordinal);
        Assert.Single(Regex.Matches(script, Regex.Escape("exec \"$CONSUMER\"")).Cast<Match>());
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
    public void CleanLanesAdapterForwardsTheScopeFlagToTheCli()
    {
        // 路径写成字面量并内联 FindRoot():ScribeTestMapDeriver 只静态解析
        // Path.Combine(XxxRepositoryLayout.FindRoot(), "字面量") 这一形式;
        // 先赋值给 root 或改用常量都会判 VariablePath → unknown → 撞 SL-003 棘轮。
        var script = File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/clean-lanes.sh"));

        // 开关必须一路透到 CLI:断链的开关比没有开关更糟——它看起来限定了作用面,
        // 实际什么也没限定,而这里限定的是「会不会删掉正在跑的判官树」。
        // 钉住转发那一行本身,不是钉住「文本里出现过这个参数名」:后者在 case 分支里
        // 也命中,删掉转发行照样绿(实测变异 EXIT=0),那是格式校验冒充指向校验。
        Assert.Contains("arguments+=(--lanes-only)", script, StringComparison.Ordinal);
        Assert.Contains("--lanes-only", script, StringComparison.Ordinal);
        var parseIndex = script.IndexOf("--lanes-only", StringComparison.Ordinal);
        var execIndex = script.IndexOf("exec dotnet run", StringComparison.Ordinal);
        Assert.True(parseIndex >= 0, "clean-lanes adapter must accept the scope flag");
        Assert.True(execIndex > parseIndex, "flag parsing must precede the CLI invocation");
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
