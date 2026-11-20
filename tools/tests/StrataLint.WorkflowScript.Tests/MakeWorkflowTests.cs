using StrataLint.Runtime;
using System.Text;
using System.Text.RegularExpressions;
using StrataLint.Engine;

namespace StrataLint.WorkflowScript.Tests;

public sealed partial class MakeWorkflowTests
{
    private const string ScribeScriptPath = "tools/scripts/scribe.sh";
    private const string ScribeReleaseScriptPath = "tools/scripts/scribe-release.sh";
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
    private const string ReanchorScriptPath = "tools/scripts/mathlib-reanchor.sh";
    private const string ReportConsumerScriptPath =
        "tools/scripts/report/report-consumer.sh";
    private const string ReportSupervisorScriptPath =
        "tools/scripts/report/report-supervisor.sh";
    private const string LeanReportInputScriptPath =
        "tools/scripts/report/lean-report-input.sh";
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
        "lean-report-scoped",
        "lean-report-prepare",
        "check-lean-report",
        "build",
        "emit",
        "dag",
        "filemap",
        "filemap-conform",
        "scribe-release",
        "scribe-release-publish",
        "scribe-release-fetch",
        "mathlib-reanchor",
        "truth-export",
        "deliver-check",
        "deposit",
        "deposit-uncovered",
        "worktree",
        "worktree-clean",
        "worktree-remove",
        "worktree-pending",
        "worktree-checkpoint",
        "worktree-publish",
        "worktree-finalize",
        "worktree-return",
        "worktree-stale",
        "pr",
        "pr-open",
        "pr-watch",
        "gate",
        "gate-plan",
        "ci-unit",
        "compiled-judge-test",
        "compiled-fib-test",
        "require-full-build",
    ];

    private static readonly string[] ToolsTargets =
    [
        "auric-fib-analysis-build",
        "auric-fib-analysis",
        "auric-fib-analysis-test",
        "auric-fib-report",
        "auric-fib-universal-test",
        "research-readouts",
        "research-readouts-test",
        "compiled-dependencies",
        "compiled-dependencies-test",
        "worktree-maintenance-install",
        "worktree-maintenance-uninstall",
        "worktree-maintenance-notify",
        "worktree-maintenance-run",
        "worktree-maintenance-status",
        "help",
        "dotnet",
        "check-fast",
        "test",
        "selftest",
        "compile-proof",
        "filemap-conform",
        "capacity-audit",
        "update-renderer-contract",
        "clean-lanes",
        "clean-all",
        "xi-quantization",
        "xi-quantization-test",
        "prime-slab-search",
        "prime-slab-test",
        "prime-slab-device-test",
        "prime-slab-verify",
        "prime-slab-mutation-test",
        "prime-slab-cpu",
        "prime-slab-cpu-test",
        "prime-slab-cpu-mutation-test",
    ];

    [Fact]
    public void ReportEntrypointsDelegateToTheSingleHostSupervisor()
    {
        var root = TestRepositoryLayout.FindRoot();
        var supervisorName = Path.GetFileName(ReportSupervisorScriptPath);
        var producer = File.ReadAllText(Path.Combine(root, LeanReportScriptPath));
        var inspector = File.ReadAllText(Path.Combine(root, "tools/lean-inspector/inspect.sh"));
        var consumer = File.ReadAllText(Path.Combine(root, ReportConsumerScriptPath));

        // Pair argument forwarding and failure propagation are exercised by LeanReportPairScriptTests.
        // Inspector owns the producer slot for both public entries and direct callers.
        Assert.Contains("tools/lean-inspector/inspect.sh", producer, StringComparison.Ordinal);
        Assert.Contains(supervisorName, inspector, StringComparison.Ordinal);
        Assert.Contains("--lean-slot", inspector, StringComparison.Ordinal);
        Assert.Contains(supervisorName, consumer, StringComparison.Ordinal);
        Assert.Contains(LeanReportInputScriptPath, consumer, StringComparison.Ordinal);
        Assert.DoesNotContain("mktemp", producer, StringComparison.Ordinal);
        Assert.Contains("mktemp", consumer, StringComparison.Ordinal);
        Assert.Contains("STRATALINT_LEAN_REPORT", consumer, StringComparison.Ordinal);
        Assert.Contains(".materials.zip", consumer, StringComparison.Ordinal);
        Assert.DoesNotContain("may be stale", consumer, StringComparison.Ordinal);
    }

    [Fact]
    public void ScribeWrapperBuildsAndConsumesOnlyItsSelectedLeanInputs()
    {
        var root = TestRepositoryLayout.FindRoot();
        var script = File.ReadAllText(Path.Combine(root, ScribeScriptPath));

        Assert.DoesNotContain("lean-inspector/inspect.sh", script, StringComparison.Ordinal);
        Assert.DoesNotContain("SCRIBE_USE_EXISTING_REPORT", script, StringComparison.Ordinal);
        Assert.Contains(ReportConsumerScriptPath, script, StringComparison.Ordinal);
        Assert.Contains("scribe-consumer", script, StringComparison.Ordinal);
        Assert.Contains(".lake/build/stratalint/scoped-lean-report.json", script, StringComparison.Ordinal);
        Assert.Contains("lean-inputs --paths-from", script, StringComparison.Ordinal);
        Assert.Contains("make lean-report-scoped", script, StringComparison.Ordinal);
        Assert.DoesNotContain("CHECK_ARGS=()", script, StringComparison.Ordinal);
        Assert.Contains("emit|emit-values) run_scribe \"$1\"", script, StringComparison.Ordinal);
        Assert.Contains("generators=(emit emit-values)", script, StringComparison.Ordinal);
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
        var script = File.ReadAllText(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/clean-lanes.sh"));

        // 开关必须一路透到 CLI:断链的开关比没有开关更糟——它看起来限定了作用面,
        // 实际什么也没限定,而这里限定的是「会不会删掉正在跑的判官树」。
        // 断言必须匹配转发行本身;仅匹配参数名也会命中 case 分支,不能证明参数已转发。
        Assert.Contains("arguments+=(--lanes-only)", script, StringComparison.Ordinal);
        Assert.Contains("--lanes-only", script, StringComparison.Ordinal);
        var parseIndex = script.IndexOf("--lanes-only", StringComparison.Ordinal);
        var execIndex = script.IndexOf("exec dotnet run", StringComparison.Ordinal);
        Assert.True(parseIndex >= 0, "clean-lanes adapter must accept the scope flag");
        Assert.True(execIndex > parseIndex, "flag parsing must precede the CLI invocation");
    }

    private static int RecipeCount(string makefile, string target) =>
        RecipeLines(makefile.Replace("\\\r\n", string.Empty, StringComparison.Ordinal)
            .Replace("\\\n", string.Empty, StringComparison.Ordinal), target).Count;

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
