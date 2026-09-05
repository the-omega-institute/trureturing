using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class DigestionFrontierProjectionTests
{
    [Fact]
    public void ProjectionIsExhaustiveDisjointAndHonorsOverlapPrecedence()
    {
        var projection = DigestionFrontierFixture.Create().Projection;
        var byId = projection.Entries.ToDictionary(
            static item => item.Entry.AtomId,
            StringComparer.Ordinal);

        Assert.Equal(8, projection.Entries.Length);
        Assert.Equal(8, projection.Entries.Select(static item => item.Entry.AtomId).Distinct().Count());
        Assert.Equal(DigestionFrontierDisposition.Quarantined, byId[DigestionFrontierFixture.QuarantinedId].PrimaryDisposition);
        Assert.Equal("missing-prerequisite", byId[DigestionFrontierFixture.QuarantinedId].PrimaryDetail);
        Assert.True(byId[DigestionFrontierFixture.QuarantinedId].IsChainChild);
        Assert.Equal(
            [DigestionFrontierFixture.ChainParentId],
            byId[DigestionFrontierFixture.QuarantinedId].ParentAtomIds.ToArray());
        Assert.Equal(DigestionFrontierDisposition.Withheld, byId[DigestionFrontierFixture.CoverWithheldId].PrimaryDisposition);
        Assert.Equal("cover-disposition", byId[DigestionFrontierFixture.CoverWithheldId].PrimaryDetail);
        Assert.Equal(DigestionFrontierDisposition.Withheld, byId[DigestionFrontierFixture.StaleId].PrimaryDisposition);
        Assert.Equal("acknowledged-stale", byId[DigestionFrontierFixture.StaleId].PrimaryDetail);
        Assert.Equal(DigestionFrontierDisposition.ChainChild, byId[DigestionFrontierFixture.ChainChildId].PrimaryDisposition);
        Assert.Equal(DigestionFrontierDisposition.ChainChild, byId[DigestionFrontierFixture.StructuralChainChildId].PrimaryDisposition);
        Assert.Equal(DigestionFrontierDisposition.NotFormalizable, byId[DigestionFrontierFixture.StructuralId].PrimaryDisposition);
        Assert.Equal("definition", byId[DigestionFrontierFixture.StructuralId].PrimaryDetail);
        Assert.Equal(DigestionFrontierDisposition.FormalizableClaim, byId[DigestionFrontierFixture.ChainParentId].PrimaryDisposition);
        Assert.Equal(DigestionFrontierDisposition.FormalizableClaim, byId[DigestionFrontierFixture.ClaimId].PrimaryDisposition);

        Assert.Equal(1, projection.Total.Quarantined);
        Assert.Equal(2, projection.Total.Withheld);
        Assert.Equal(2, projection.Total.ChainChild);
        Assert.Equal(1, projection.Total.NotFormalizable);
        Assert.Equal(2, projection.Total.FormalizableClaim);
        Assert.Equal(8, projection.Total.ResidualOpen);
        Assert.Equal(2, projection.Total.FormalizationFrontier);
    }

    [Fact]
    public void TheoremChainChildNeverEntersTheFormalizationFrontier()
    {
        var projection = DigestionFrontierFixture.Create().Projection;

        Assert.DoesNotContain(
            projection.FormalizationFrontier,
            static item => item.Entry.AtomId == DigestionFrontierFixture.ChainChildId);
        Assert.Contains(
            projection.FormalizationFrontier,
            static item => item.Entry.AtomId == DigestionFrontierFixture.ChainParentId);
    }
}
