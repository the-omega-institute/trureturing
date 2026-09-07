using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ScribeCoverageDeltaTests
{
    [Fact]
    public void AdmissionRuleAcceptsCandidateNewCoverageWithoutScribeReceipt()
    {
        var fixture = new CoverageWithoutScribeFixture();
        fixture.Baseline = CoverageWithoutScribeFixture.Map(fixture.Baseline, entry => entry with { Coverage = [] });
        fixture.Document = CoverageWithoutScribeFixture.Map(fixture.Document, entry => entry with
        {
            ProjectedStatus = new DigestionStatus(DigestionMigrationState.Absorbed, DigestionTruthState.Closed),
        });
        var context = AdmissionContext(fixture,
            RawChangeSet.CreateWithKinds([
                (CoverageWithoutScribeFixture.EntryPath(fixture.Baseline.RequireDigestionEntries()[0]), RawChangeKind.Deleted),
                (CoverageWithoutScribeFixture.EntryPath(fixture.First), RawChangeKind.Added),
            ]));

        var findings = BackfillInventoryRule.EvaluateCandidateDelta(context);

        Assert.Empty(findings);
    }

    [Fact]
    public void AdmissionRuleLeaves84UnchangedMissingScribeReceiptsNonBlocking()
    {
        var fixture = new CoverageWithoutScribeFixture(84);
        var context = AdmissionContext(fixture, RawChangeSet.Create(["notes/unrelated.txt"]));

        var findings = BackfillInventoryRule.EvaluateCandidateDelta(context);

        Assert.Empty(findings);
    }

    [Fact]
    public void ChangedCoverageStatementWithoutScribeReceiptIsAccepted()
    {
        var fixture = new CoverageWithoutScribeFixture();
        fixture.Baseline = CoverageWithoutScribeFixture.Map(fixture.Baseline, entry => entry with
        {
            Coverage = [entry.Coverage[0] with { TargetStatementId = null }],
        });
        fixture.Document = CoverageWithoutScribeFixture.Map(fixture.Document, entry => entry with
        {
            ProjectedStatus = new DigestionStatus(DigestionMigrationState.Absorbed, DigestionTruthState.Closed),
        });
        var repository = fixture.Gateway(RawChangeSet.Create([CoverageWithoutScribeFixture.EntryPath(fixture.First)]));

        var result = DigestStatusCommand.Run(repository, new FakeLeanReportSource(fixture.Inputs.Report),
            new FakeScribeEmissionVerifier(fixture.Verified), ["--base", "baseline"],
            FakeAtomHistorySource.ForPaths(fixture.Files.Keys), new DigestAgeClock());

        Assert.True(result.Success, result.Error);
        Assert.Contains("absorbed-closed", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("scribe-", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void FullScanAbsorbsCompleteCoverageWithoutScribeReceipts()
    {
        var fixture = new CoverageWithoutScribeFixture(84);
        var repository = fixture.Gateway(RawChangeSet.Create([]));

        var result = DigestStatusCommand.Run(repository, new FakeLeanReportSource(fixture.Inputs.Report),
            new FakeScribeEmissionVerifier(fixture.Verified), ["--base", "baseline"],
            FakeAtomHistorySource.ForPaths(fixture.Files.Keys), new DigestAgeClock());

        Assert.True(result.Success, result.Error);
        Assert.Equal(84, result.Output.Split('\n').Count(line =>
            line.StartsWith("ENTRY ", StringComparison.Ordinal)
                && line.Contains("absorbed-closed", StringComparison.Ordinal)));
        Assert.DoesNotContain("scribe-", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void CandidateNewCoverageWithoutScribeReceiptIsAccepted()
    {
        var fixture = new CoverageWithoutScribeFixture();
        fixture.Baseline = CoverageWithoutScribeFixture.Map(fixture.Baseline, entry => entry with { Coverage = [] });
        fixture.Document = CoverageWithoutScribeFixture.Map(fixture.Document, entry => entry with
        {
            ProjectedStatus = new DigestionStatus(DigestionMigrationState.Absorbed, DigestionTruthState.Closed),
        });
        var repository = fixture.Gateway(RawChangeSet.Create([CoverageWithoutScribeFixture.EntryPath(fixture.First)]));

        var result = DigestStatusCommand.Run(repository, new FakeLeanReportSource(fixture.Inputs.Report),
            new FakeScribeEmissionVerifier(fixture.Verified), ["--base", "baseline"],
            FakeAtomHistorySource.ForPaths(fixture.Files.Keys), new DigestAgeClock());

        Assert.True(result.Success, result.Error);
        Assert.Contains("absorbed-closed", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("scribe-", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void UnrelatedDeltaRetainsPartialBaselineWithoutScribeGaps()
    {
        var fixture = new CoverageWithoutScribeFixture(84);
        var repository = fixture.Gateway(RawChangeSet.Create(["notes/unrelated.txt"]));

        var result = DigestStatusCommand.Run(repository, new FakeLeanReportSource(fixture.Inputs.Report),
            new FakeScribeEmissionVerifier(fixture.Verified), ["--base", "baseline"],
            FakeAtomHistorySource.ForPaths(fixture.Files.Keys), new DigestAgeClock());

        Assert.True(result.Success, result.Error);
        Assert.Equal(84, result.Output.Split('\n').Count(line =>
            line.StartsWith("ENTRY ", StringComparison.Ordinal)
                && line.Contains("partial-closed", StringComparison.Ordinal)));
        Assert.DoesNotContain("scribe-", result.Output, StringComparison.Ordinal);
    }

    private static RuleEvaluationContext AdmissionContext(CoverageWithoutScribeFixture fixture, RawChangeSet changes)
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

internal sealed class CoverageWithoutScribeFixture
{
    internal const string ModuleGid = "D5/S0/Carrier/Probe";
    internal CoverInputs Inputs { get; set; }
    internal Dictionary<string, string> Files { get; }
    internal BackfillInventoryDocument Document { get; set; }
    internal BackfillInventoryDocument Baseline { get; set; }
    internal VerifiedScribeEmissions Verified { get; set; }
    internal DigestionLedgerEntry First => Document.RequireDigestionEntries()[0];

    internal CoverageWithoutScribeFixture(int count = 1)
    {
        const string gid = ModuleGid + ".probe";
        Inputs = CoverWorld.Materialize(new CoverSpec
        {
            ModuleGid = ModuleGid,
            Declaration = "probe",
            InitialCoverage = [gid],
            Migration = "partial",
            Truth = "closed",
            BaselineTargetIdentical = true,
        });
        Files = new Dictionary<string, string>(Inputs.Files, StringComparer.Ordinal);
        Files[TheoryAtomizerDataLoader.DataPath] = Encoding.UTF8.GetString(DigestionTestSupport.RulesBytes);
        Verified = Inputs.VerifiedEmissions!;
        var template = Assert.Single(Inputs.Document.RequireDigestionEntries());
        Files.Remove(DigestionCasStore.RootPath + template.AtomId);
        var entries = Enumerable.Range(0, count).Select(index =>
        {
            var bytes = Encoding.UTF8.GetBytes($"synthetic receipt obligation {ModuleGid} {index}\n");
            var fingerprint = DigestionFingerprint.Compute(bytes);
            var id = fingerprint.RawSha256["sha256:".Length..];
            Files[DigestionCasStore.RootPath + id] = Encoding.UTF8.GetString(bytes);
            return template with
            {
                AtomId = id,
                Atomizer = AtomizerRegistry.NoAtomizerId,
                Fingerprints = fingerprint,
                CasRef = fingerprint.RawSha256,
            };
        }).ToImmutableArray();
        var source = Assert.Single(Inputs.Document.RequireDigestionSources()) with
        {
            Atomizer = AtomizerRegistry.NoAtomizerId,
            GenreRegistryProjection = GenreRegistryProjection.Available(GenreRegistryCheck.NoGenreRegistry),
            Entries = entries,
        };
        Document = Inputs.Document.WithDigestionSources([source]);
        Baseline = Document;
    }

    internal static BackfillInventoryDocument Map(
        BackfillInventoryDocument document,
        Func<DigestionLedgerEntry, DigestionLedgerEntry> transform) =>
        document.WithDigestionSources(document.RequireDigestionSources().Select(source =>
            source with { Entries = source.Entries.Select(transform).ToImmutableArray() }).ToImmutableArray());

    internal RawRepositorySnapshot Raw(BackfillInventoryDocument document)
    {
        var files = new Dictionary<string, string>(Files, StringComparer.Ordinal);
        DirectoryLedgerTestSupport.ReplaceWithProjection(files, document);
        return RawRepositorySnapshot.Create(files.Select(static pair =>
            RawRepositoryEntry.FromText(pair.Key, pair.Value)));
    }

    internal FakeRepositoryGateway Gateway(RawChangeSet changes) =>
        new(changes, Raw(Document), Raw(Baseline));

    internal static string EntryPath(DigestionLedgerEntry entry) =>
        BackfillInventoryLoader.RootPath + entry.SourceId + "/"
        + DigestionStatusNames.Migration(entry.ProjectedStatus.Migration) + "-"
        + DigestionStatusNames.Truth(entry.ProjectedStatus.Truth) + "/" + entry.AtomId + ".yaml";
}
