using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ReceiptApplicabilityClassifierTests
{
    [Theory]
    [InlineData("unknown-plane")]
    [InlineData("missing-report")]
    [InlineData("missing-module-report")]
    [InlineData("report-error")]
    [InlineData("missing-frozen-authority")]
    public void ClassifierRejectsUnavailableAuthority(string failure)
    {
        var fixture = new ScribeSeedFixture();
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(fixture.Raw(fixture.Document))).Snapshot;
        Assert.True(Gid.TryParse(ScribeSeedFixture.DeclarationGid, out var gid));
        LeanAxiomReport? report = fixture.Inputs.Report;
        FrozenStatementIndex? frozen = FrozenStatementIndex.Create(FrozenStateCatalog.Load(snapshot), report);
        var validation = CurrentEdgeValidator.Validate(gid.Value, snapshot, report,
            LeanTruthStates.Resolve(snapshot, AcceptedLeanClosure.Create(report)), frozen);
        switch (failure)
        {
            case "unknown-plane": Assert.False(Gid.TryParse("D5/Q/Unknown", out gid)); break;
            case "missing-report": report = null; break;
            case "missing-module-report": report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>()); break;
            case "report-error": report = LeanAxiomReport.Create(report.Files.ToDictionary(
                pair => pair.Key.Value, pair => pair.Value with { Error = "unavailable" })); break;
            case "missing-frozen-authority": frozen = null; break;
        }

        Assert.IsType<ReceiptApplicability.Failure>(ReceiptApplicability.Classify(gid, validation, snapshot, report, frozen));
    }

    [Fact]
    public void RequiredClassificationUsesResolutionInsteadOfStoredNullTarget()
    {
        var fixture = new ScribeSeedFixture();
        fixture.Document = ScribeSeedFixture.Map(fixture.Document, entry => entry with
        { Coverage = [entry.Coverage[0] with { TargetStatementId = null }] });
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(fixture.Raw(fixture.Document))).Snapshot;
        Assert.True(Gid.TryParse(fixture.First.Coverage[0].Gid, out var gid));
        var report = fixture.Inputs.Report;
        var frozen = FrozenStatementIndex.Create(FrozenStateCatalog.Load(snapshot), report);
        var edge = CurrentEdgeValidator.Validate(gid.Value, snapshot, report,
            LeanTruthStates.Resolve(snapshot, AcceptedLeanClosure.Create(report)), frozen);

        Assert.IsType<ReceiptApplicability.Required>(ReceiptApplicability.Classify(gid, edge, snapshot, report, frozen));
    }
}
