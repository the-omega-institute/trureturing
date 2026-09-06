using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ScribeSeedCommandTests
{
    [Theory]
    [InlineData(true)]
    [InlineData(false)]
    public void WaivedSeedIsNotApplicableAndNeverWrites(bool dryRun)
    {
        var fixture = ReceiptApplicabilityFixture.Create(waived: true);
        fixture.Files.Remove(ScribeEmissionAttestation.DefinitionPath(ScribeSeedFixture.ModuleGid));
        fixture.Verified = VerifiedScribeEmissions.Empty;
        string[] arguments = ["--seed-missing", "--atom", fixture.First.AtomId, "--gid",
            ScribeSeedFixture.DeclarationGid, "--base", "baseline", .. dryRun ? new[] { "--dry-run" } : []];

        var execution = Execute(fixture, arguments);

        Assert.Equal(dryRun, execution.Result.Success);
        Assert.Contains("eligibility=not-applicable", execution.Result.Output, StringComparison.Ordinal);
        Assert.Equal(0, execution.ApplyCalls);
        Assert.Equal(Image(execution.Before), Image(execution.After));
    }

    [Fact]
    public void SeedNonFormalPairRemainsInvalidInput()
    {
        var fixture = new ScribeSeedFixture();
        var execution = Execute(fixture, ["--seed-missing", "--atom", fixture.First.AtomId,
            "--gid", "D5/E/values--json", "--base", "baseline", "--dry-run"]);

        Assert.False(execution.Result.Success);
        Assert.Contains("SEED_PAIRS_INVALID", execution.Result.Error, StringComparison.Ordinal);
        Assert.Equal(0, execution.ApplyCalls);
    }

    [Fact]
    public void SeedHeaderFailureIsAnErrorEvenInDryRun()
    {
        var fixture = new ScribeSeedFixture();
        ReceiptApplicabilityFixture.Header(fixture, "none(waiver:)");
        var execution = Execute(fixture, ["--seed-missing", "--atom", fixture.First.AtomId,
            "--gid", ScribeSeedFixture.DeclarationGid, "--base", "baseline", "--dry-run"]);

        Assert.False(execution.Result.Success);
        Assert.Contains("scribe-applicability-invalid", execution.Result.Error, StringComparison.Ordinal);
        Assert.Equal(0, execution.ApplyCalls);
    }
}
