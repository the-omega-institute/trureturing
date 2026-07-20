using System.Text.RegularExpressions;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class MakeWorkflowTests
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
    private const string IngestScriptPath = "Meta/StrataLint/scripts/ingest.sh";
    private const string ReportConsumerScriptPath =
        "Meta/StrataLint/scripts/report/report-consumer.sh";
    private const string ReportSupervisorScriptPath =
        "Meta/StrataLint/scripts/report/report-supervisor.sh";
    private const string LeanReportInputScriptPath =
        "Meta/StrataLint/scripts/report/lean-report-input.sh";
    private const string LeanReportPairScriptPath = "Meta/StrataLint/scripts/lean-report-pair.sh";
    private const string PerfReportScriptPath = "Meta/StrataLint/scripts/perf-report.sh";
    private const string PerfEventScriptPath = "Meta/StrataLint/scripts/perf-event-lib.sh";

    private static readonly string[] Targets =
    [
        "help",
        "dotnet",
        "test",
        "lean",
        "lean-report",
        "build",
        "c0-renew",
        "clean-lanes",
        "emit",
        "emit-check",
        "ingest",
        "record-golden",
        "selftest",
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
        Assert.Contains("lake build", Recipe(makefile, "lean"), StringComparison.Ordinal);
        Assert.Contains(LeanReportScriptPath, Recipe(makefile, "lean-report"), StringComparison.Ordinal);
        Assert.Contains(ScribeScriptPath + " emit", Recipe(makefile, "emit"), StringComparison.Ordinal);
        Assert.Contains(ScribeScriptPath + " check", Recipe(makefile, "emit-check"), StringComparison.Ordinal);
        Assert.DoesNotContain("ingest: emit-check", makefile, StringComparison.Ordinal);
        Assert.Contains(IngestScriptPath, Recipe(makefile, "ingest"), StringComparison.Ordinal);
        Assert.Contains("golden-record", Recipe(makefile, "record-golden"), StringComparison.Ordinal);
        Assert.Contains(SelftestScriptPath, Recipe(makefile, "selftest"), StringComparison.Ordinal);
        Assert.Contains(LocalHarnessGateScriptPath, Recipe(makefile, "gate"), StringComparison.Ordinal);
        Assert.Contains(PerfReportScriptPath, Recipe(makefile, "perf-report"), StringComparison.Ordinal);
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
        Assert.Contains("make -C candidate selftest", workflow, StringComparison.Ordinal);
        Assert.Contains("make -C \"$CANDIDATE_ROOT\" emit-check", localGate, StringComparison.Ordinal);
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
        Assert.Contains(
            "dotnet \"$JUDGE_DLL\" check --protected-base",
            sharedGate,
            StringComparison.Ordinal);
        Assert.Contains(
            "dotnet \"$CANDIDATE_DLL\" verify-conservative",
            sharedGate,
            StringComparison.Ordinal);
        Assert.DoesNotContain(
            "dotnet \"$JUDGE_DLL\" verify-conservative",
            sharedGate,
            StringComparison.Ordinal);
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
