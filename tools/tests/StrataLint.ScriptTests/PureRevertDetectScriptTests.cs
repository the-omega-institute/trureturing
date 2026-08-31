using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class PureRevertDetectScriptTests
{
    [Fact]
    public void ExactToolsOnlyMergeInverseAfterUnrelatedCommitIsAccepted()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles("seed target", new FileMutation("tools/target.txt", "before\n"));
        var feature = fixture.CommitOnBranch(
            "feature",
            "target transition",
            new FileMutation("tools/target.txt", "after\n"));
        var target = fixture.MergeIntoMain(feature, "merge target");
        fixture.CommitFiles("later unrelated", new FileMutation("tools/later.txt", "later\n"));
        fixture.CommitCandidateAndMerge(
            "exact inverse",
            new FileMutation("tools/target.txt", "before\n"));

        var result = Run([fixture.Repository]);

        Assert.Equal(0, result.ExitCode);
        Assert.Empty(result.StandardError);
        var output = Encoding.UTF8.GetString(result.StandardOutput);
        Assert.Equal(1, output.Count(static character => character == '\n'));
        Assert.Contains($"base_sha={fixture.BaseSha}", output, StringComparison.Ordinal);
        Assert.Contains($"head_sha={fixture.HeadSha}", output, StringComparison.Ordinal);
        Assert.Contains($"target_merge_sha={target}", output, StringComparison.Ordinal);
        Assert.Contains("changed_path_count=1", output, StringComparison.Ordinal);
    }

    [Fact]
    public void WrongTargetHintCannotOverrideIndependentlyLocatedTarget()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles("seed target", new FileMutation("tools/target.txt", "before\n"));
        var feature = fixture.CommitOnBranch(
            "feature",
            "target transition",
            new FileMutation("tools/target.txt", "after\n"));
        var target = fixture.MergeIntoMain(feature, "merge target");
        fixture.CommitCandidateAndMerge(
            "exact inverse",
            new FileMutation("tools/target.txt", "before\n"));

        var result = Run([fixture.Repository, fixture.RootSha]);

        Assert.Equal(0, result.ExitCode);
        Assert.Contains(
            $"target_merge_sha={target}",
            Encoding.UTF8.GetString(result.StandardOutput),
            StringComparison.Ordinal);
    }

    [Fact]
    public void ExactInverseOfSingleParentFirstParentCommitIsRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles("seed target", new FileMutation("tools/target.txt", "before\n"));
        fixture.CommitFiles("ordinary target", new FileMutation("tools/target.txt", "after\n"));
        fixture.CommitCandidateAndMerge(
            "exact inverse of ordinary commit",
            new FileMutation("tools/target.txt", "before\n"));

        AssertRejected(Run([fixture.Repository]), "PURE_REVERT_TARGET_NOT_A_MERGE");
    }

    [Fact]
    public void SingleParentExactWitnessDoesNotHideUniqueMergeWitness()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles("seed target", new FileMutation("tools/target.txt", "before\n"));
        var feature = fixture.CommitOnBranch(
            "feature",
            "merge target transition",
            new FileMutation("tools/target.txt", "after\n"));
        var target = fixture.MergeIntoMain(feature, "merge target");
        fixture.CommitFiles(
            "restore before ordinary target",
            new FileMutation("tools/target.txt", "before\n"));
        fixture.CommitFiles(
            "ordinary target transition",
            new FileMutation("tools/target.txt", "after\n"));
        fixture.CommitCandidateAndMerge(
            "exact inverse",
            new FileMutation("tools/target.txt", "before\n"));

        var result = Run([fixture.Repository]);

        Assert.Equal(0, result.ExitCode);
        Assert.Empty(result.StandardError);
        Assert.Contains(
            $"target_merge_sha={target}",
            Encoding.UTF8.GetString(result.StandardOutput),
            StringComparison.Ordinal);
    }

    [Fact]
    public void ExactWorkflowMergeInverseIsAccepted()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        var workflowPath = ".github/" + "work" + "flows/" + "build.yml";
        fixture.CommitFiles(
            "seed workflow",
            new FileMutation(workflowPath, "before\n"));
        var feature = fixture.CommitOnBranch(
            "feature",
            "workflow feature",
            new FileMutation(workflowPath, "after\n"));
        var target = fixture.MergeIntoMain(feature, "merge workflow");
        fixture.CommitCandidateAndMerge(
            "exact workflow inverse",
            new FileMutation(workflowPath, "before\n"));

        var result = Run([fixture.Repository]);

        Assert.Equal(0, result.ExitCode);
        Assert.Empty(result.StandardError);
        Assert.Contains(
            $"target_merge_sha={target}",
            Encoding.UTF8.GetString(result.StandardOutput),
            StringComparison.Ordinal);
    }

    [Fact]
    public void ExactExecutableMergeInverseIsAccepted()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles(
            "seed executable",
            new FileMutation("tools/run.sh", "before\n", Executable: true));
        var feature = fixture.CommitOnBranch(
            "feature",
            "executable feature",
            new FileMutation("tools/run.sh", "after\n", Executable: true));
        var target = fixture.MergeIntoMain(feature, "merge executable");
        fixture.CommitCandidateAndMerge(
            "exact executable inverse",
            new FileMutation("tools/run.sh", "before\n", Executable: true));

        var result = Run([fixture.Repository]);

        Assert.Equal(0, result.ExitCode);
        Assert.Empty(result.StandardError);
        Assert.Contains(
            $"target_merge_sha={target}",
            Encoding.UTF8.GetString(result.StandardOutput),
            StringComparison.Ordinal);
    }

    [Fact]
    public void NoOpMergeResultIsRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles("seed", new FileMutation("tools/target.txt", "value\n"));
        fixture.CommitEmptyCandidateAndMerge("no-op candidate");

        AssertRejected(Run([fixture.Repository]), "PURE_REVERT_NO_CHANGES");
    }

    [Fact]
    public void AncientAncestorTreeRestorationWithoutSingleExactTransitionIsRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles(
            "ancient tree",
            new FileMutation("tools/one.txt", "one-before\n"),
            new FileMutation("tools/two.txt", "two-before\n"));
        fixture.CommitFiles("change one", new FileMutation("tools/one.txt", "one-after\n"));
        fixture.CommitFiles("change two", new FileMutation("tools/two.txt", "two-after\n"));
        fixture.CommitCandidateAndMerge(
            "restore ancient tree",
            new FileMutation("tools/one.txt", "one-before\n"),
            new FileMutation("tools/two.txt", "two-before\n"));

        AssertRejected(Run([fixture.Repository]), "PURE_REVERT_NOT_INVERSE");
    }

    [Fact]
    public void ExactSecondParentTransitionIsRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles("seed", new FileMutation("tools/target.txt", "before\n"));
        var secondParent = fixture.CommitOnBranch(
            "feature",
            "second parent transition",
            new FileMutation("tools/target.txt", "after\n"));
        var resolutionTree = fixture.CommitOnBranch(
            "resolution-tree",
            "conflict resolution tree",
            new FileMutation("tools/target.txt", "resolution\n"));
        fixture.MergeTreeIntoMain(secondParent, resolutionTree, "merge with resolution");
        fixture.CommitFiles("later target rewrite", new FileMutation("tools/target.txt", "after\n"));
        fixture.CommitCandidateAndMerge(
            "inverse second parent only",
            new FileMutation("tools/target.txt", "before\n"));

        AssertRejected(
            Run([fixture.Repository, secondParent]),
            "PURE_REVERT_SECOND_PARENT");
    }

    [Fact]
    public void PartialInverseIsRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles(
            "seed",
            new FileMutation("tools/one.txt", "one-before\n"),
            new FileMutation("tools/two.txt", "two-before\n"));
        fixture.CommitFiles(
            "two-path target",
            new FileMutation("tools/one.txt", "one-after\n"),
            new FileMutation("tools/two.txt", "two-after\n"));
        fixture.CommitCandidateAndMerge(
            "partial inverse",
            new FileMutation("tools/one.txt", "one-before\n"));

        AssertRejected(Run([fixture.Repository]), "PURE_REVERT_NOT_INVERSE");
    }

    [Fact]
    public void InverseWithAdditionalPathIsRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles("seed", new FileMutation("tools/target.txt", "before\n"));
        fixture.CommitFiles("target", new FileMutation("tools/target.txt", "after\n"));
        fixture.CommitCandidateAndMerge(
            "inverse plus extra",
            new FileMutation("tools/target.txt", "before\n"),
            new FileMutation("tools/extra.txt", "extra\n"));

        AssertRejected(Run([fixture.Repository]), "PURE_REVERT_NOT_INVERSE");
    }

    [Fact]
    public void TargetPathModifiedLaterIsRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles("seed", new FileMutation("tools/target.txt", "before\n"));
        fixture.CommitFiles("target", new FileMutation("tools/target.txt", "target\n"));
        fixture.CommitFiles("later rewrite", new FileMutation("tools/target.txt", "later\n"));
        fixture.CommitCandidateAndMerge(
            "unclean inverse",
            new FileMutation("tools/target.txt", "before\n"));

        AssertRejected(Run([fixture.Repository]), "PURE_REVERT_NOT_INVERSE");
    }

    [Fact]
    public void ExactInverseOutsideCanonicalHarnessAllowlistIsRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles(
            "seed ledger",
            new FileMutation("Golden/Frozen/accepted/node.json", "before\n"));
        fixture.CommitFiles(
            "ledger target",
            new FileMutation("Golden/Frozen/accepted/node.json", "after\n"));
        fixture.CommitCandidateAndMerge(
            "ledger inverse",
            new FileMutation("Golden/Frozen/accepted/node.json", "before\n"));

        AssertRejected(
            Run([fixture.Repository]),
            "PURE_REVERT_PATH_OUTSIDE_ALLOWLIST");
    }
}
