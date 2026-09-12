using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    private const string DeletedAdmissionPath = "retired/component.txt";

    [Theory]
    [InlineData("judge", false)]
    [InlineData("judge", true)]
    [InlineData("content", false)]
    [InlineData("content", true)]
    public void DeletedPathUsesBaselineEvenWhenCandidateRegistrationDisagrees(
        string deletedPlane, bool candidateRegistersPath)
    {
        var baseline = DeletionSnapshot(Manifest((DeletedAdmissionPath, deletedPlane)), includePath: true);
        var candidate = DeletionSnapshot(candidateRegistersPath
            ? Manifest((DeletedAdmissionPath, deletedPlane == "judge" ? "content" : "judge"))
            : Manifest((FileMapPath, "judge")));

        var decision = AdmissionPlanePolicy.Evaluate(baseline, candidate, [DeletedAdmissionPath]);
        var outcome = ProductionCliEnvironment.EvaluateAdmissionPlane(
            baseline, candidate, RawChangeSet.CreateWithKinds([(DeletedAdmissionPath, RawChangeKind.Deleted)]));

        Assert.True(decision.IsAdmissible, decision.Message);
        Assert.Equal(deletedPlane == "judge"
            ? AdmissionPlaneClassification.JudgeOnly : AdmissionPlaneClassification.ContentOnly,
            decision.Classification);
        Assert.Equal(deletedPlane == "judge", decision.RequiresFullEngineering());
        Assert.Null(outcome);
    }

    [Theory]
    [InlineData(null, "ADMISSION-PLANE-FILEMAP-UNAVAILABLE")]
    [InlineData("", "ADMISSION-PLANE-PATH-MATCH-COUNT")]
    [InlineData("[[files]]\npattern = 'other.txt'\nadmission_plane = 'judge'", "ADMISSION-PLANE-PATH-MATCH-COUNT")]
    [InlineData("[[files]]\npattern = '**'\nadmission_plane = 'judge'\n[[files]]\npattern = 'retired/*'\nadmission_plane = 'content'", "ADMISSION-PLANE-PATH-MATCH-COUNT")]
    [InlineData("[[files]]\npattern = '**'", "ADMISSION-PLANE-FILEMAP-INVALID")]
    [InlineData("[[files]]\npattern = '**'\nadmission_plane = 'observer'", "ADMISSION-PLANE-FILEMAP-INVALID")]
    [InlineData("[[files]]\npattern = 'retired/?.txt'\nadmission_plane = 'judge'", "FILEMAP-PATTERN-UNSAFE")]
    [InlineData("files = [", "ADMISSION-PLANE-FILEMAP-INVALID")]
    public void DeletedPathRequiresUniqueValidBaselineRegistration(string? baselineManifest, string expectedCode)
    {
        var baseline = DeletionSnapshot(baselineManifest, includePath: true);
        var candidate = DeletionSnapshot(Manifest((FileMapPath, "judge"), (DeletedAdmissionPath, "judge")));

        var decision = AdmissionPlanePolicy.Evaluate(baseline, candidate, [DeletedAdmissionPath]);
        var outcome = ProductionCliEnvironment.EvaluateAdmissionPlane(
            baseline, candidate, RawChangeSet.CreateWithKinds([(DeletedAdmissionPath, RawChangeKind.Deleted)]));

        Assert.False(decision.IsAdmissible);
        Assert.Equal(expectedCode, decision.Code);
        Assert.Null(decision.Classification);
        Assert.Throws<InvalidOperationException>(() => decision.RequiresFullEngineering());
        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("protected-base", failure.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(null, "ADMISSION-PLANE-FILEMAP-UNAVAILABLE")]
    [InlineData("files = [", "ADMISSION-PLANE-FILEMAP-INVALID")]
    [InlineData("[[files]]\npattern = 'unrelated'", "ADMISSION-PLANE-FILEMAP-INVALID")]
    [InlineData("[[files]]\npattern = 'unrelated'\nadmission_plane = 'observer'", "ADMISSION-PLANE-FILEMAP-INVALID")]
    public void CandidateMetadataMustBeValidEvenWhenEveryChangedPathIsDeleted(
        string? candidateManifest, string expectedCode)
    {
        var baseline = DeletionSnapshot(Manifest((DeletedAdmissionPath, "judge")), includePath: true);
        var candidate = DeletionSnapshot(candidateManifest);

        var decision = AdmissionPlanePolicy.Evaluate(baseline, candidate, [DeletedAdmissionPath]);
        var outcome = ProductionCliEnvironment.EvaluateAdmissionPlane(
            baseline, candidate, RawChangeSet.CreateWithKinds([(DeletedAdmissionPath, RawChangeKind.Deleted)]));

        Assert.False(decision.IsAdmissible);
        Assert.Equal(expectedCode, decision.Code);
        var failure = Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.DoesNotContain("protected-base", failure.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void DeletedPathRejectsNonUtf8ManifestOnEitherSide(bool invalidBaseline)
    {
        var invalid = AdmissionPlaneSnapshot([0xff]);
        var baseline = invalidBaseline
            ? RawRepositorySnapshot.Create(invalid.Entries.Append(RawRepositoryEntry.FromText(DeletedAdmissionPath, "old")))
            : DeletionSnapshot(Manifest((DeletedAdmissionPath, "judge")), includePath: true);
        var candidate = invalidBaseline ? DeletionSnapshot(Manifest((FileMapPath, "judge"))) : invalid;

        var decision = AdmissionPlanePolicy.Evaluate(baseline, candidate, [DeletedAdmissionPath]);

        Assert.False(decision.IsAdmissible);
        Assert.Equal("ADMISSION-PLANE-FILEMAP-INVALID", decision.Code);
        Assert.Contains("bytes are not strict UTF-8", decision.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(true, true)]
    [InlineData(false, true)]
    [InlineData(false, false)]
    public void CandidateRegistrationMissDoesNotEstablishDeletion(bool baselineHasPath, bool candidateHasPath)
    {
        var baseline = DeletionSnapshot(Manifest((DeletedAdmissionPath, "judge")), baselineHasPath);
        var candidate = DeletionSnapshot(Manifest((FileMapPath, "judge")), candidateHasPath);

        var decision = AdmissionPlanePolicy.Evaluate(baseline, candidate, [DeletedAdmissionPath]);
        // Even a claimed deletion cannot replace the two snapshots' presence evidence.
        var outcome = ProductionCliEnvironment.EvaluateAdmissionPlane(
            baseline, candidate, RawChangeSet.CreateWithKinds([(DeletedAdmissionPath, RawChangeKind.Deleted)]));

        Assert.False(decision.IsAdmissible);
        Assert.Equal("ADMISSION-PLANE-PATH-MATCH-COUNT", decision.Code);
        Assert.IsType<AdmissionOutcome.InfrastructureFailure>(outcome);
        Assert.DoesNotContain("protected-base", decision.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData(false, "judge")]
    [InlineData(true, "content")]
    public void PresentPathsUseCandidateWithoutLoadingInvalidBaseline(bool baselineHasPath, string plane)
    {
        var baseline = DeletionSnapshot("files = [", baselineHasPath);
        var candidate = DeletionSnapshot(Manifest((DeletedAdmissionPath, plane)), includePath: true);

        var decision = AdmissionPlanePolicy.Evaluate(baseline, candidate, [DeletedAdmissionPath]);

        Assert.True(decision.IsAdmissible, decision.Message);
        Assert.Equal(plane == "judge", decision.RequiresFullEngineering());
    }

    [Fact]
    public void RealGitRenameUsesBaselineSourceAndCandidateDestinationRegistrations()
    {
        const string source = "judge/source.txt";
        const string destination = "content/destination.txt";
        using var repository = new TemporaryDirectory();
        ReviewRegressionTests.RunGit(repository.Path, "init");
        ReviewRegressionTests.RunGit(repository.Path, "config", "user.email", "stratalint@example.invalid");
        ReviewRegressionTests.RunGit(repository.Path, "config", "user.name", "StrataLint Tests");
        Directory.CreateDirectory(Path.Combine(repository.Path, "judge"));
        Directory.CreateDirectory(Path.Combine(repository.Path, "content"));
        Directory.CreateDirectory(Path.Combine(repository.Path, "Meta"));
        File.WriteAllText(Path.Combine(repository.Path, source), "renamed component\n");
        File.WriteAllText(Path.Combine(repository.Path, FileMapPath),
            Manifest((FileMapPath, "judge"), (source, "judge")));
        ReviewRegressionTests.RunGit(repository.Path, "add", ".");
        ReviewRegressionTests.RunGit(repository.Path, "commit", "-m", "baseline");
        var baseline = ReviewRegressionTests.RunGit(repository.Path, "rev-parse", "HEAD").Trim();
        File.Move(Path.Combine(repository.Path, source), Path.Combine(repository.Path, destination));
        File.WriteAllText(Path.Combine(repository.Path, FileMapPath),
            Manifest((FileMapPath, "judge"), (destination, "content")));
        ReviewRegressionTests.RunGit(repository.Path, "add", ".");
        ReviewRegressionTests.RunGit(repository.Path, "commit", "-m", "candidate");
        var gateway = new GitRepositoryGateway(repository.Path);
        var prepared = gateway.Prepare(baseline);

        var outcome = ProductionCliEnvironment.EvaluateAdmissionPlane(
            gateway.ReadRevision(prepared.Revision), gateway.ReadCurrent(), prepared.Changes);

        Assert.Contains(prepared.Changes.Entries, change => change.Path.Value == source && change.Kind == RawChangeKind.Deleted);
        Assert.Contains(prepared.Changes.Entries, change => change.Path.Value == destination && change.Kind == RawChangeKind.Added);
        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        Assert.Contains(rejected.Diagnostics, static item => item.Message.Contains("ADMISSION-PLANE-MIXED", StringComparison.Ordinal));
    }

    private static RawRepositorySnapshot DeletionSnapshot(string? manifest, bool includePath = false)
    {
        var snapshot = AdmissionPlaneSnapshot(manifest is null ? null : Encoding.UTF8.GetBytes(manifest));
        return includePath
            ? RawRepositorySnapshot.Create(snapshot.Entries.Append(RawRepositoryEntry.FromText(DeletedAdmissionPath, "component\n")))
            : snapshot;
    }
}
