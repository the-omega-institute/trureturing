using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ScribeReceiptScopeTests
{
    [Fact]
    public void UnrelatedEntryOutsideClosureIsNotJudgedEvenWhenLoaded()
    {
        var fixture = ReceiptApplicabilityFixture.Create();

        var evaluation = ReceiptApplicabilityFixture.Evaluate(fixture, RawChangeSet.Create(["notes/unrelated.txt"]));

        Assert.False(Assert.Single(evaluation.Entries).StatusAuthorityChanged);
        Assert.DoesNotContain(evaluation.Findings, message => message.Contains("coverage-scribe-receipt-required", StringComparison.Ordinal));
    }

    [Theory]
    [InlineData("entry")]
    [InlineData("definition")]
    [InlineData("chain")]
    public void EntryInsideAffectedClosureIsJudged(string dependency)
    {
        var fixture = ReceiptApplicabilityFixture.Create();
        var path = ScribeSeedFixture.EntryPath(fixture.First);
        if (dependency == "definition") path = ScribeEmissionAttestation.DefinitionPath(ScribeSeedFixture.ModuleGid);
        if (dependency == "chain")
        {
            var child = new ScribeSeedFixture(moduleGid: "D5/S0/Carrier/Child");
            foreach (var file in child.Files) fixture.Files[file.Key] = file.Value;
            fixture.Inputs = fixture.Inputs with { Report = LeanAxiomReport.Create(
                fixture.Inputs.Report.Files.Concat(child.Inputs.Report.Files)
                    .ToDictionary(pair => pair.Key.Value, pair => pair.Value)) };
            var parent = fixture.First with { Receipts = fixture.First.Receipts with { ChainAtoms = [child.First.AtomId] } };
            var source = Assert.Single(fixture.Document.RequireDigestionSources());
            fixture.Document = fixture.Document.WithDigestionSources([source with { Entries = [parent, child.First with { Coverage = [] }] }]);
            path = ScribeSeedFixture.EntryPath(child.First);
        }

        var evaluation = ReceiptApplicabilityFixture.Evaluate(fixture, RawChangeSet.Create([path]));

        Assert.True(evaluation.Entries.Single(item => item.Entry.AtomId == fixture.First.AtomId).StatusAuthorityChanged);
        Assert.Contains(evaluation.Findings, message => message.Contains("coverage-scribe-receipt-required", StringComparison.Ordinal)
            && message.Contains(fixture.First.AtomId, StringComparison.Ordinal));
    }

    [Fact]
    public void RuleImplementationChangeDoesNotExpandReceiptGateToPopulation()
    {
        var fixture = ReceiptApplicabilityFixture.Create();
        var evaluation = ReceiptApplicabilityFixture.Evaluate(fixture, RawChangeSet.Create([
            "tools/StrataLint.Engine/Digestion/Evaluation/DigestionStatusEvaluator.ScribeCoverage.cs"]));

        Assert.False(Assert.Single(evaluation.Entries).StatusAuthorityChanged);
        Assert.DoesNotContain(evaluation.Findings, message => message.Contains("coverage-scribe-receipt-required", StringComparison.Ordinal));
    }

    [Fact]
    public void DigestStatusImplementationChangeDoesNotExpandReceiptGateToPopulation()
    {
        var fixture = ReceiptApplicabilityFixture.Create();
        var result = DigestStatusCommand.Run(
            fixture.Gateway(RawChangeSet.Create([
                "tools/StrataLint.Engine/Rules/RuleEngine.cs"])),
            new FakeLeanReportSource(fixture.Inputs.Report),
            new FakeScribeEmissionVerifier(fixture.Verified),
            ["--base", "baseline"],
            FakeAtomHistorySource.ForEntries([]),
            new DigestAgeClock());

        Assert.True(result.Success, result.Error);
        Assert.DoesNotContain(
            "coverage-scribe-receipt-required",
            result.Output,
            StringComparison.Ordinal);
    }

    [Fact]
    public void DigestStatusHarmlessTargetChangeDoesNotPromoteHistoricalDeclarationReferenceDebt()
    {
        var fixture = ReceiptApplicabilityFixture.Create(waived: true);
        ReceiptApplicabilityFixture.Receipts(fixture, 1);
        fixture.Baseline = fixture.Document;
        Assert.True(fixture.Verified.TryGet(ScribeSeedFixture.ModuleGid, out var emission));
        fixture.Verified = VerifiedScribeEmissions.Create([emission]);
        var changes = RawChangeSet.Create([ScribeSeedFixture.ModuleGid + ".lean"]);
        var verifier = new FakeScribeEmissionVerifier(fixture.Verified);

        var result = DigestStatusCommand.Run(
            fixture.Gateway(changes),
            new FakeLeanReportSource(fixture.Inputs.Report),
            verifier,
            ["--base", "baseline"],
            FakeAtomHistorySource.ForEntries([]),
            new DigestAgeClock());

        Assert.True(result.Success, result.Error);
        Assert.DoesNotContain("DIGEST_STATUS_INVALID", result.Error, StringComparison.Ordinal);
        Assert.DoesNotContain(
            verifier.LastChanges!.Paths,
            static path => path.Value == ScribeSeedFixture.ModuleGid + ".lean");
    }
}
