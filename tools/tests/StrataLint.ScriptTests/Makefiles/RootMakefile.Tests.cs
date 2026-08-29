namespace StrataLint.ScriptTests;

[ScriptSubject("Makefile")]
public sealed partial class RootMakefileTests
{
    private const string ScribeScriptPath = "tools/scripts/scribe.sh";
    private const string LocalHarnessGateScriptPath = "tools/scripts/local-harness-gate.sh";
    private const string PreflightScriptPath = "tools/scripts/preflight.sh";
    private const string ScribeContentChecksScriptPath = "tools/scripts/workflow/scribe-content-checks.sh";
    private const string WorktreeInitScriptPath = "tools/scripts/worktree-init.sh";
    private const string CleanLanesScriptPath = "tools/scripts/clean-lanes.sh";
    private const string LeanReportScriptPath = "tools/scripts/report/lean-report.sh";
    private const string LeanCacheEnsureScriptPath = "tools/scripts/worktree/lean-cache-ensure.sh";
    private const string LeanCacheRunScriptPath = "tools/scripts/worktree/lean-cache-run.sh";
    private const string WarmDonorScriptPath = "tools/scripts/worktree/warm-donor.sh";
    private const string IngestScriptPath = "tools/scripts/ingest.sh";
    private const string EchoResidualSummaryScriptPath = "tools/scripts/report/echo-residual-summary.sh";
    private const string PrOpenScriptPath = "tools/scripts/pr.sh open";
    private const string PrWatchScriptPath = "tools/scripts/pr.sh watch";

    private static readonly string[] RootTargets =
    [
        "help", "test", "lean-cache-ensure", "lean-cache-to-github-without-mathlib",
        "lean-cache-from-github-without-mathlib", "warm-donor", "lean", "lean-report",
        "build", "emit", "ingest", "align-digestion-status", "echo-residual-summary",
        "show-atom", "theory-candidates", "truth-export", "deliver-check", "receipts-stage",
        "deposit", "cover", "cover-batch", "worktree", "worktree-clean", "pr-open",
        "pr-watch", "preflight", "gate",
    ];

    private static readonly string[] ToolsTargets =
    [
        "help", "dotnet", "test", "engineering-tests", "selftest",
        "update-renderer-contract", "clean-lanes",
    ];

    [Fact]
    public void PlaybookTargetsAreHelpedAndDelegateToOneCanonicalScript()
    {
        var makefile = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("Makefile"));
        var script = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("tools/scripts/workflow/playbook-workflows.sh"));

        foreach (var target in new[] { "deliver-check", "receipts-stage" })
        {
            Assert.Contains($"make {target}", makefile, StringComparison.Ordinal);
            Assert.Contains(
                $"scripts/workflow/playbook-workflows.sh {target} \"$(BASE)\"",
                makefile,
                StringComparison.Ordinal);
        }

        foreach (var target in new[] { "deposit", "cover" })
        {
            Assert.Contains($"make {target} ATOM_ID=", makefile, StringComparison.Ordinal);
            Assert.Contains(
                $"scripts/workflow/playbook-workflows.sh {target} \"$(BASE)\" \"$(ATOM_ID)\" \"$(GID)\"",
                makefile,
                StringComparison.Ordinal);
        }

        Assert.Contains("make cover-batch ATOMS=", makefile, StringComparison.Ordinal);
        Assert.Contains(
            "scripts/workflow/playbook-workflows.sh cover-batch \"$(BASE)\" \"$(ATOMS)\"",
            makefile,
            StringComparison.Ordinal);

        Assert.Contains("ledger-append --candidate-lean-report", script, StringComparison.Ordinal);
        Assert.Contains("digest-status --base", script, StringComparison.Ordinal);
    }

    [Fact]
    public void LeanCacheTargetsDelegateToTheCanonicalScript()
    {
        var makefile = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("Makefile"));
        foreach (var verb in new[] { "publish", "fetch" })
        {
            var recipe = Assert.Single(
                makefile.Split('\n'),
                line => line.Contains("lean-cache-publish.sh " + verb, StringComparison.Ordinal));
            Assert.StartsWith("\t", recipe, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void HelpRunsAndNamesEveryRootTarget()
    {
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run(
            "make",
            ["help"],
            root,
            StrataLint.Engine.BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);

        Assert.Equal(0, result.ExitCode);
        var output = System.Text.Encoding.UTF8.GetString(result.StandardOutput);
        Assert.All(RootTargets, target => Assert.Contains($"make {target}", output, StringComparison.Ordinal));
        Assert.Contains("values", output, StringComparison.OrdinalIgnoreCase);
        Assert.DoesNotContain("make dotnet", output, StringComparison.Ordinal);
        Assert.DoesNotContain("make tools-test", output, StringComparison.Ordinal);
        Assert.DoesNotContain("pr-update", output, StringComparison.Ordinal);
    }

    [Fact]
    public void WorktreeTargetKeepsItsPathAndArgumentContract()
    {
        var makefile = TestRepositoryLayout.ReadAllText(
            RepositoryRelativePath.Create("Makefile"));

        Assert.Contains("WORKTREE_DEST = $(if $(DEST)", makefile, StringComparison.Ordinal);
        Assert.Contains("[DEST=DIR]", makefile, StringComparison.Ordinal);
        Assert.Contains("\"$(KIND)\" \"$(NAME)\"", makefile, StringComparison.Ordinal);
        Assert.DoesNotContain("$(origin PATH)", makefile, StringComparison.Ordinal);
    }

    private static int RecipeCount(string makefile, string target) => RecipeLines(makefile, target).Count;

    private static string Recipe(string makefile, string target) => Assert.Single(RecipeLines(makefile, target));

    private static IReadOnlyList<string> RecipeLines(string makefile, string target)
    {
        var lines = makefile.Split('\n');
        var start = Array.FindIndex(lines, line => line.StartsWith(target + ":", StringComparison.Ordinal));
        Assert.True(start >= 0, $"target is absent: {target}");
        return lines.Skip(start + 1)
            .TakeWhile(static line => line.Length == 0 || line[0] == '\t')
            .Where(static line => line.StartsWith('\t'))
            .ToArray();
    }
}
