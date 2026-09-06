using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ScribeCoverageDeltaTests
{
    [Fact]
    public void AdmissionRuleRejectsCandidateNewCoverageWithoutScribeReceipt()
    {
        var fixture = new ScribeSeedFixture();
        fixture.Baseline = ScribeSeedFixture.Map(fixture.Baseline, entry => entry with { Coverage = [] });
        var context = AdmissionContext(fixture,
            RawChangeSet.Create([ScribeSeedFixture.EntryPath(fixture.First)]));

        var findings = BackfillInventoryRule.EvaluateCandidateDelta(context);

        var finding = Assert.Single(findings, finding =>
            finding.Message.Contains("coverage-scribe-receipt-required", StringComparison.Ordinal));
        var descriptor = Assert.Single(RuleCatalog.Default.Descriptors, rule => rule.Id == RuleId.CreateKnown(16));
        Assert.Equal(AdmissionEffect.Block, finding.Effect ?? descriptor.AdmissionEffect);
        Assert.Contains(fixture.First.AtomId, finding.Message, StringComparison.Ordinal);
        Assert.Contains(ScribeSeedFixture.DeclarationGid, finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AdmissionRuleLeaves84UnchangedMissingScribeReceiptsNonBlocking()
    {
        var fixture = new ScribeSeedFixture(84);
        var context = AdmissionContext(fixture, RawChangeSet.Create(["notes/unrelated.txt"]));

        var findings = BackfillInventoryRule.EvaluateCandidateDelta(context);

        Assert.Empty(findings);
    }

    [Fact]
    public void ChangedCoverageStatementWithoutScribeReceiptIsRejected()
    {
        var fixture = new ScribeSeedFixture();
        fixture.Baseline = ScribeSeedFixture.Map(fixture.Baseline, entry => entry with
        {
            Coverage = [entry.Coverage[0] with { TargetStatementId = null }],
        });
        var repository = fixture.Gateway(RawChangeSet.Create([ScribeSeedFixture.EntryPath(fixture.First)]));

        var result = DigestStatusCommand.Run(repository, new FakeLeanReportSource(fixture.Inputs.Report),
            new FakeScribeEmissionVerifier(fixture.Verified), ["--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains("coverage-scribe-receipt-required", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void FullScanStillUsesProtectedBaseEdgeValuesForReceiptDebt()
    {
        var fixture = new ScribeSeedFixture(84);
        var repository = fixture.Gateway(RawChangeSet.Create([]));

        var result = DigestStatusCommand.Run(repository, new FakeLeanReportSource(fixture.Inputs.Report),
            new FakeScribeEmissionVerifier(fixture.Verified), ["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        Assert.Equal(84, result.Output.Split('\n').Count(line =>
            line.Contains("gaps=scribe-receipt-missing", StringComparison.Ordinal)));
    }

    [Fact]
    public void CandidateNewCoverageWithoutScribeReceiptIsRejected()
    {
        var fixture = new ScribeSeedFixture();
        fixture.Baseline = ScribeSeedFixture.Map(fixture.Baseline, entry => entry with { Coverage = [] });
        var repository = fixture.Gateway(RawChangeSet.Create([ScribeSeedFixture.EntryPath(fixture.First)]));

        var result = DigestStatusCommand.Run(repository, new FakeLeanReportSource(fixture.Inputs.Report),
            new FakeScribeEmissionVerifier(fixture.Verified), ["--base", "baseline"]);

        Assert.False(result.Success);
        Assert.Contains("coverage-scribe-receipt-required", result.Error, StringComparison.Ordinal);
        Assert.Contains(fixture.First.AtomId, result.Error, StringComparison.Ordinal);
        Assert.Contains(ScribeSeedFixture.DeclarationGid, result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void UnrelatedDeltaWith84MissingScribeReceiptsIsNonBlockingAndObservable()
    {
        var fixture = new ScribeSeedFixture(84);
        var repository = fixture.Gateway(RawChangeSet.Create(["notes/unrelated.txt"]));

        var result = DigestStatusCommand.Run(repository, new FakeLeanReportSource(fixture.Inputs.Report),
            new FakeScribeEmissionVerifier(fixture.Verified), ["--base", "baseline"]);

        Assert.True(result.Success, result.Error);
        Assert.Equal(84, result.Output.Split('\n').Count(line =>
            line.Contains("gaps=scribe-receipt-missing", StringComparison.Ordinal)));
        Assert.DoesNotContain("coverage-scribe-receipt-required", result.Output, StringComparison.Ordinal);
    }

    private static RuleEvaluationContext AdmissionContext(ScribeSeedFixture fixture, RawChangeSet changes)
    {
        var repository = fixture.Gateway(changes);
        var current = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(repository.ReadCurrent())).Snapshot;
        var baseline = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(repository.ReadRevision("baseline"))).Snapshot;
        var policy = RegistryLoadAssert.Accepted(RegistryLoader.Load(
            Encoding.UTF8.GetBytes(TestRegistry.Canonical), Encoding.UTF8.GetBytes(TestRegistry.Domains))).Policy;
        var lean = Assert.IsType<LeanValidationOutcome.Accepted>(
            LeanClosureValidator.Validate(current, fixture.Inputs.Report)).Capability;
        var bootstrap = Assert.IsType<BootstrapOutcome.Clear>(BootstrapGate.Evaluate(changes));
        return RuleEvaluationContext.Create(current, baseline, policy, lean, changes,
            MetaEvaluationProfile.ForClear(bootstrap.Capability), fixture.Verified);
    }
}
