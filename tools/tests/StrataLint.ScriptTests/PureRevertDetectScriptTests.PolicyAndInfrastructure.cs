namespace StrataLint.Tests;

public sealed partial class PureRevertDetectScriptTests
{
    [Fact]
    public void AdditionalProtectedPolicyPrefixIsNotImplicitlyReversible()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles("seed other", new FileMutation("other/target.txt", "before\n"));
        fixture.CommitFiles("other target", new FileMutation("other/target.txt", "after\n"));
        fixture.CommitCandidateAndMerge(
            "other inverse",
            new FileMutation("other/target.txt", "before\n"));

        AssertRejected(Run([fixture.Repository]), "PURE_REVERT_PATH_OUTSIDE_ALLOWLIST");
    }

    [Fact]
    public void MissingToolsProtectionPolicyAtomFailsClosed()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.RemoveProtectionPolicyAtom("tools");
        fixture.CommitFiles("seed target", new FileMutation("tools/target.txt", "before\n"));
        var feature = fixture.CommitOnBranch(
            "feature",
            "target transition",
            new FileMutation("tools/target.txt", "after\n"));
        fixture.MergeIntoMain(feature, "merge target");
        fixture.CommitCandidateAndMerge(
            "exact inverse",
            new FileMutation("tools/target.txt", "before\n"));

        AssertRejected(Run([fixture.Repository]), "PURE_REVERT_HISTORY_UNAVAILABLE");
    }

    [Fact]
    public void MissingWorkflowsProtectionPolicyAtomFailsClosed()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        var workflowPath = ".github/" + "work" + "flows/target.yml";
        fixture.RemoveProtectionPolicyAtom("workflows");
        fixture.CommitFiles("seed workflow", new FileMutation(workflowPath, "before\n"));
        var feature = fixture.CommitOnBranch(
            "feature",
            "workflow transition",
            new FileMutation(workflowPath, "after\n"));
        fixture.MergeIntoMain(feature, "merge workflow");
        fixture.CommitCandidateAndMerge(
            "exact inverse",
            new FileMutation(workflowPath, "before\n"));

        AssertRejected(Run([fixture.Repository]), "PURE_REVERT_HISTORY_UNAVAILABLE");
    }

    [Fact]
    public void BlobRestorationWithoutModeRestorationIsRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles(
            "seed mode",
            new FileMutation("tools/mode.sh", "before\n", Executable: false));
        fixture.CommitFiles(
            "content and mode target",
            new FileMutation("tools/mode.sh", "after\n", Executable: true));
        fixture.CommitCandidateAndMerge(
            "blob-only inverse",
            new FileMutation("tools/mode.sh", "before\n", Executable: true));

        AssertRejected(Run([fixture.Repository]), "PURE_REVERT_NOT_INVERSE");
    }

    [Fact]
    public void GitlinkPointerMismatchIsRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        var first = fixture.CreateDetachedCommit("gitlink one");
        var second = fixture.CreateDetachedCommit("gitlink two");
        var third = fixture.CreateDetachedCommit("gitlink three");
        fixture.CommitGitlink("seed gitlink", "tools/link", first);
        fixture.CommitGitlink("target gitlink", "tools/link", second);
        fixture.CommitGitlinkCandidateAndMerge("wrong gitlink inverse", "tools/link", third);

        AssertRejected(Run([fixture.Repository]), "PURE_REVERT_NOT_INVERSE");
    }

    [Fact]
    public void ForgedRevertMessageWithoutInverseTreeIsRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles("seed", new FileMutation("tools/target.txt", "before\n"));
        fixture.CommitFiles("target", new FileMutation("tools/target.txt", "after\n"));
        fixture.CommitCandidateAndMerge(
            "Revert \"target\"",
            new FileMutation("tools/target.txt", "forged\n"));

        AssertRejected(Run([fixture.Repository]), "PURE_REVERT_NOT_INVERSE");
    }

    [Fact]
    public void MultipleExactSingleParentTargetsFailClosedAsNotMerges()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles("seed", new FileMutation("tools/target.txt", "before\n"));
        fixture.CommitFiles("first target", new FileMutation("tools/target.txt", "after\n"));
        fixture.CommitFiles("restore", new FileMutation("tools/target.txt", "before\n"));
        fixture.CommitFiles("second target", new FileMutation("tools/target.txt", "after\n"));
        fixture.CommitCandidateAndMerge(
            "inverse with two witnesses",
            new FileMutation("tools/target.txt", "before\n"));

        AssertRejected(Run([fixture.Repository]), "PURE_REVERT_TARGET_NOT_A_MERGE");
    }

    [Fact]
    public void CandidateThatChangesClassifierItselfIsRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles(
            "seed classifier",
            new FileMutation(
                "tools/scripts/workflow/pure-revert-detect.sh",
                "before\n"));
        fixture.CommitFiles(
            "classifier target",
            new FileMutation(
                "tools/scripts/workflow/pure-revert-detect.sh",
                "after\n"));
        fixture.CommitCandidateAndMerge(
            "classifier inverse",
            new FileMutation(
                "tools/scripts/workflow/pure-revert-detect.sh",
                "before\n"));

        AssertRejected(Run([fixture.Repository]), "PURE_REVERT_CLASSIFIER_MODIFIED");
    }

    [Fact]
    public void ShallowRepositoryFailsClosed()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles("seed", new FileMutation("tools/target.txt", "before\n"));
        fixture.CommitFiles("target", new FileMutation("tools/target.txt", "after\n"));
        fixture.CommitCandidateAndMerge(
            "inverse",
            new FileMutation("tools/target.txt", "before\n"));
        var shallow = fixture.CreateShallowClone();

        AssertRejected(Run([shallow]), "PURE_REVERT_HISTORY_UNAVAILABLE");
    }

    [Fact]
    public void MissingFirstParentObjectFailsClosed()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles("seed", new FileMutation("tools/target.txt", "before\n"));
        var missing = fixture.Head();
        fixture.CommitFiles("target", new FileMutation("tools/target.txt", "after\n"));
        fixture.CommitCandidateAndMerge(
            "inverse",
            new FileMutation("tools/target.txt", "before\n"));
        fixture.DeleteLooseObject(missing);

        AssertRejected(Run([fixture.Repository]), "PURE_REVERT_HISTORY_UNAVAILABLE");
    }

    [Fact]
    public void MissingArgumentsAreRejected()
    {
        if (OperatingSystem.IsWindows()) return;

        AssertRejected(Run([]), "PURE_REVERT_BAD_ARGUMENT");
    }

    [Fact]
    public void ExtraArgumentsAreRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();

        AssertRejected(
            Run([fixture.Repository, fixture.RootSha, "unexpected"]),
            "PURE_REVERT_BAD_ARGUMENT");
    }

    [Fact]
    public void ReversedRepositoryAndHintArgumentsAreRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();

        AssertRejected(
            Run([fixture.RootSha, fixture.Repository]),
            "PURE_REVERT_BAD_ARGUMENT");
    }

    [Fact]
    public void GitCommandFailureFailsClosedWithNamedReason()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles("seed", new FileMutation("tools/target.txt", "before\n"));
        fixture.CommitFiles("target", new FileMutation("tools/target.txt", "after\n"));
        fixture.CommitCandidateAndMerge(
            "inverse",
            new FileMutation("tools/target.txt", "before\n"));
        var failingGitPath = fixture.CreateFailingGitPath("diff-tree");

        AssertRejected(
            Run([fixture.Repository], failingGitPath),
            "PURE_REVERT_GIT_FAILURE");
    }
}
