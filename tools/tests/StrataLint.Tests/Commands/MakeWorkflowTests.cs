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
    private const string CheckFastFilterVariable = "CHECK_FAST_FILTER :=";
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
        "mathlib-reanchor",
        "echo-residual-summary",
        "digestion-readiness",
        "show-atom",
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
        "check-fast",
        "test",
        "engineering-tests",
        "engineering-tests-base-cwd",
        "selftest",
        "capacity-audit",
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
        Assert.Contains("mathlib-reanchor)", script, StringComparison.Ordinal);
        Assert.Contains("make -C \"$ROOT\" lean-report", script, StringComparison.Ordinal);
        Assert.Contains("git -C \"$ROOT\" merge-base HEAD \"$BASE\"", script, StringComparison.Ordinal);
        Assert.Contains(
            "ledger-reanchor-mathlib --base \"$base_sha\"",
            script,
            StringComparison.Ordinal);
        Assert.Equal(
            2,
            Regex.Matches(script, Regex.Escape("exec \"$CONSUMER\"")).Count);
    }

    [Fact]
    public void IngestWrapperDerivesReportInputStateFromExecutableClosureDelta()
    {
        if (OperatingSystem.IsWindows()) return;

        const string leanSource = "theorem probe : True := by trivial\n";
        var root = TestRepositoryLayout.FindRoot();
        using var fixture = new TemporaryDirectory();
        var binDirectory = Path.Combine(fixture.Path, "bin");
        var ingestPath = Path.Combine(fixture.Path, IngestScriptPath);
        var inputPath = Path.Combine(fixture.Path, LeanReportInputScriptPath);
        Directory.CreateDirectory(binDirectory);
        Directory.CreateDirectory(Path.GetDirectoryName(ingestPath)!);
        Directory.CreateDirectory(Path.GetDirectoryName(inputPath)!);
        Directory.CreateDirectory(Path.Combine(fixture.Path, "D5"));
        Directory.CreateDirectory(Path.Combine(fixture.Path, "tools", "StrataLint.Cli"));
        File.Copy(Path.Combine(root, IngestScriptPath), ingestPath);
        File.Copy(Path.Combine(root, LeanReportInputScriptPath), inputPath);
        File.WriteAllText(Path.Combine(fixture.Path, "Trureturing.lean"), "import D5.Probe\n");
        File.WriteAllText(Path.Combine(fixture.Path, "D5", "Probe.lean"), leanSource);
        File.WriteAllText(Path.Combine(fixture.Path, "lean-toolchain"), "leanprover/lean4:v4.31.0\n");
        File.WriteAllText(Path.Combine(fixture.Path, "lake-manifest.json"), "{\"version\":\"1.1.0\"}\n");
        File.WriteAllText(Path.Combine(fixture.Path, "lakefile.toml"), "name = \"Fixture\"\n");
        File.WriteAllText(Path.Combine(fixture.Path, "README.md"), "baseline\n");
        var dotnetPath = Path.Combine(binDirectory, "dotnet");
        File.WriteAllText(
            dotnetPath,
            """
            #!/usr/bin/env bash
            if [[ "${1:-}" == "msbuild" ]]; then exit 1; fi
            printf '%s\n' "$*"
            """ + "\n");
        foreach (var executable in new[] { ingestPath, inputPath, dotnetPath })
        {
            File.SetUnixFileMode(
                executable,
                UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        }

        ReviewRegressionTests.RunGit(fixture.Path, "init", "--quiet");
        ReviewRegressionTests.RunGit(fixture.Path, "config", "user.email", "stratalint@example.invalid");
        ReviewRegressionTests.RunGit(fixture.Path, "config", "user.name", "StrataLint Tests");
        ReviewRegressionTests.RunGit(fixture.Path, "add", ".");
        ReviewRegressionTests.RunGit(fixture.Path, "commit", "--quiet", "-m", "ingest wrapper fixture");

        ProcessOutput RunWrapper() => TestProcessRunner.Run(
            "/bin/bash",
            [
                "-c",
                "PATH=\"$1:$PATH\" XDG_CACHE_HOME=\"$2\" exec \"$3\" ingest HEAD",
                "ingest-wrapper",
                binDirectory,
                Path.Combine(fixture.Path, "cache"),
                ingestPath,
            ],
            fixture.Path,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);

        File.AppendAllText(Path.Combine(fixture.Path, "D5", "Probe.lean"), "-- closure delta\n");
        var changed = RunWrapper();
        Assert.Equal(0, changed.ExitCode);
        Assert.Contains(
            "ingest --base HEAD --report-input-state changed",
            System.Text.Encoding.UTF8.GetString(changed.StandardOutput),
            StringComparison.Ordinal);

        File.WriteAllText(Path.Combine(fixture.Path, "D5", "Probe.lean"), leanSource);
        File.AppendAllText(Path.Combine(fixture.Path, "README.md"), "markdown-only delta\n");
        var unchanged = RunWrapper();
        Assert.Equal(0, unchanged.ExitCode);
        Assert.Contains(
            "ingest --base HEAD --report-input-state unchanged",
            System.Text.Encoding.UTF8.GetString(unchanged.StandardOutput),
            StringComparison.Ordinal);
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
