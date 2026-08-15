using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ProductionEnvironmentTests
{
    [Fact]
    public void CheckRejectsAnUnregisteredGenreBehindInheritedReceipts()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var baselineBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**定理 1.1(A)**。old。\n");
        var candidateBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**定理 1.1(A)**。old。\n\n**未登记体 2.1(B)**。new。\n");
        var atom = Assert.Single(AtomizerRegistry.Atomize(
            atomizerId,
            baselineBytes,
            DigestionTestSupport.Rules).Claims);
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(candidateBytes);
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(baselineBytes);
        InstallLedger(fixture, IngestLedger(atomizerId, atom), atom);

        var outcome = CheckGenreCandidate(fixture);

        AssertUnregisteredGenreRejection(outcome);
    }

    [Fact]
    public void CheckRejectsAnUnregisteredGenreBehindAMatchingCoarseReceipt()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var atomizerId = SyntheticNumberedAtomizer.Id;
        var baselineBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**定理 1.1(A)**。old。\n");
        var candidateBytes = Encoding.UTF8.GetBytes(
            "# Synthetic\n\n**定理 1.1(A)**。old。\n\n**未登记体 2.1(B)**。new。\n");
        var rawBytes = ImmutableArray.CreateRange(candidateBytes);
        var coarse = new DigestionAtom(
            "coarse/source",
            0,
            candidateBytes.Length,
            rawBytes,
            DigestionFingerprint.ComputeOpaque(rawBytes.AsSpan()),
            []);
        var candidateLedger = IngestLedger(atomizerId, coarse);
        var baselineLedger = EmptyRegisteredLedger(atomizerId);
        var captured = DigestionCasStore.Capture(rawBytes.AsSpan());
        var capturedText = Encoding.UTF8.GetString(captured.Bytes.AsSpan());
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(candidateBytes);
        fixture.Baseline[RuleFixture.FixtureDigestionSourcePath] = Encoding.UTF8.GetString(baselineBytes);
        DirectoryLedgerTestSupport.ReplaceWithProjection(fixture.Files, candidateLedger);
        DirectoryLedgerTestSupport.ReplaceWithProjection(fixture.Baseline, baselineLedger);
        fixture.Files.Remove(RuleFixture.FixtureCasPath);
        fixture.Baseline.Remove(RuleFixture.FixtureCasPath);
        fixture.Files[captured.RelativePath] = capturedText;
        fixture.Baseline[captured.RelativePath] = capturedText;

        var outcome = CheckGenreCandidate(fixture);

        AssertUnregisteredGenreRejection(outcome);
    }

    private static AdmissionOutcome CheckGenreCandidate(RuleFixture fixture)
    {
        var environment = new ProductionCliEnvironment(
            "/repo",
            new FakeRepositoryGateway(
                RawChangeSet.Create([RuleFixture.FixtureDigestionSourcePath]),
                Snapshot(fixture.Files),
                Snapshot(fixture.Baseline)),
            new FakeLeanReportSource(null));
        return CheckWithReports(environment, fixture);
    }

    private static void AssertUnregisteredGenreRejection(AdmissionOutcome outcome)
    {
        var rejected = Assert.IsType<AdmissionOutcome.RuleRejected>(outcome);
        var finding = Assert.Single(rejected.Diagnostics.Where(diagnostic =>
            diagnostic.RuleId == RuleId.CreateKnown(16)
            && diagnostic.Message.Contains(
                "source fixture-source uses claim genres its dialect does not register",
                StringComparison.Ordinal)));
        Assert.Contains("未登记体", finding.Message, StringComparison.Ordinal);
        Assert.Contains(TheoryAtomizerDataLoader.DataPath, finding.Message, StringComparison.Ordinal);
    }

    private static string EmptyRegisteredLedger(string atomizerId) => $$"""
        schema_version: 3
        ledger: theory-digestion-v1
        sources:
          - source_id: fixture-source
            path: {{RuleFixture.FixtureDigestionSourcePath}}
            atomizer: {{atomizerId}}
            acknowledged_stale: []
            entries: []
        ticket_index: []
        """;
}
