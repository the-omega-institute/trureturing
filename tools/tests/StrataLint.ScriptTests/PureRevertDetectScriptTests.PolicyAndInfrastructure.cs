namespace StrataLint.Tests;

public sealed partial class PureRevertDetectScriptTests
{
    [Fact]
    public void ExactNonHarnessMergeInverseIsAccepted()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles("seed other", new FileMutation("other/target.txt", "before\n"));
        var feature = fixture.CommitOnBranch(
            "feature",
            "other target",
            new FileMutation("other/target.txt", "after\n"));
        var target = fixture.MergeIntoMain(feature, "merge other target");
        fixture.CommitCandidateAndMerge(
            "other inverse",
            new FileMutation("other/target.txt", "before\n"));

        var result = Run([fixture.Repository]);

        Assert.Equal(0, result.ExitCode);
        Assert.Empty(result.StandardError);
        Assert.Contains(
            $"target_merge_sha={target}",
            System.Text.Encoding.UTF8.GetString(result.StandardOutput),
            StringComparison.Ordinal);
    }

    [Fact]
    public void CiModePublishesConfirmedMarkerAndOutputs()
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
        var outputPath = fixture.ScratchPath("confirmed-output");
        var timeoutPath = fixture.CreateTimeoutPath(expire: false);

        var result = Run(
            ["--ci", fixture.Repository, outputPath],
            timeoutPath);

        Assert.Equal(0, result.ExitCode);
        Assert.True(result.StandardError.Length == 0, Diagnostics(result));
        Assert.Equal(
            $"PURE_REVERT_GATE confirmed=true target_merge_sha={target} changed_path_count=1\n",
            System.Text.Encoding.UTF8.GetString(result.StandardOutput));
        Assert.Equal(
            [
                "classification=confirmed",
                $"target_merge_sha={target}",
                "changed_path_count=1",
                "confirmed=true",
            ],
            ScriptHarnessScratch.ReadScratchLines(outputPath));
    }

    [Fact]
    public void CiModeTreatsDetectorTimeoutAsNotApplicable()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        var outputPath = fixture.ScratchPath("timeout-output");
        var timeoutPath = fixture.CreateTimeoutPath(expire: true);

        var result = Run(
            ["--ci", fixture.Repository, outputPath],
            timeoutPath);

        Assert.Equal(0, result.ExitCode);
        Assert.True(result.StandardError.Length == 0, Diagnostics(result));
        Assert.Equal(
            "PURE_REVERT_GATE confirmed=false classification=not_applicable detector_exit=124\n",
            System.Text.Encoding.UTF8.GetString(result.StandardOutput));
        Assert.Equal(
            ["confirmed=false", "classification=not_applicable"],
            ScriptHarnessScratch.ReadScratchLines(outputPath));
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
