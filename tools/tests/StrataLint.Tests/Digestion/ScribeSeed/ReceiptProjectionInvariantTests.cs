using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class ReceiptProjectionInvariantTests
{
    [Fact]
    public void UnrelatedChangePreservesPersistedStatusesAcrossReceiptApplicabilityClasses()
    {
        var required = new ScribeSeedFixture(moduleGid: "D5/S0/Carrier/InvariantRequired");
        AddValidReceipts(required);
        SetStatus(required, DigestionMigrationState.Absorbed, DigestionTruthState.Closed);

        var notApplicable = new ScribeSeedFixture(moduleGid: "D5/S0/Carrier/InvariantWaived");
        SetWaiver(notApplicable);

        var pending = new ScribeSeedFixture(moduleGid: "D5/S0/Carrier/InvariantPending");
        var pendingState = FrozenStatePath.FromModulePath(
            RepoPath.CreateKnown("D5/S0/Carrier/InvariantPending.lean")).Value;
        pending.Files.Remove(pendingState);
        pending.Document = ScribeSeedFixture.Map(pending.Document, static entry => entry with
        {
            Coverage = [entry.Coverage[0] with { TargetStatementId = null }],
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Partial,
                DigestionTruthState.Open),
        });

        var optionalReceipt = new ScribeSeedFixture(
            moduleGid: "D5/S0/Carrier/InvariantOptionalReceipt");
        SetWaiver(optionalReceipt);
        AddValidReceipts(optionalReceipt);
        SetStatus(optionalReceipt, DigestionMigrationState.Absorbed, DigestionTruthState.Closed);

        var chain = new ScribeSeedFixture(
            count: 2,
            moduleGid: "D5/S0/Carrier/InvariantChain");
        AddValidReceipts(chain);
        var chainEntries = chain.Document.RequireDigestionEntries();
        chain.Document = ScribeSeedFixture.Map(chain.Document, entry => entry with
        {
            Receipts = entry.AtomId == chainEntries[1].AtomId
                ? entry.Receipts with { ChainAtoms = [chainEntries[0].AtomId] }
                : entry.Receipts,
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Absorbed,
                DigestionTruthState.Closed),
        });

        var fixtures = new[] { required, notApplicable, pending, optionalReceipt, chain };
        var document = Combine(fixtures);
        var changes = RawChangeSet.Create(["notes/unrelated-receipt-projection.txt"]);
        var repository = new FakeRepositoryGateway(
            changes,
            Raw(required, document),
            Raw(required, document));
        var current = Decode(repository.ReadCurrent());
        var baseline = Decode(repository.ReadRevision("baseline"));
        var reportSource = new FakeLeanReportSource(CombineReports(fixtures));
        var report = reportSource.Load(current);

        var evaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.ChangedSet,
            document,
            current,
            AcceptedLeanClosure.Create(report),
            CombineEmissions(fixtures),
            baselineDocument: document,
            baselineSnapshot: baseline,
            changes: changes,
            projectedStatusChanges: changes,
            receiptGateChanges: changes);

        var mismatches = evaluation.Entries
            .Where(static entry => entry.DerivedStatus != entry.Entry.ProjectedStatus)
            .ToArray();
        Assert.Equal(6, evaluation.Entries.Length);
        Assert.Empty(mismatches);
        Assert.All(evaluation.Entries, static entry =>
            Assert.Equal(entry.Entry.ProjectedStatus, entry.DerivedStatus));
        Assert.Contains(
            evaluation.Entries.Single(entry => entry.Entry.AtomId == notApplicable.First.AtomId)
                .ReceiptObservations,
            static observation => observation.Code == "scribe-not-applicable:mirror-waiver");
        Assert.Contains(
            evaluation.Entries.Single(entry => entry.Entry.AtomId == pending.First.AtomId)
                .ReceiptObservations,
            static observation => observation.Code == "scribe-pending-target");
    }

    private static void AddValidReceipts(ScribeSeedFixture fixture)
    {
        var gid = fixture.First.Coverage[0].Gid;
        var documentGid = ScribeEmissionAttestation.DocumentGid(gid);
        Assert.True(fixture.Verified.TryGet(documentGid, out var record));
        fixture.Document = ScribeSeedFixture.Map(fixture.Document, entry => entry with
        {
            Receipts = entry.Receipts with
            {
                Scribe =
                [
                    new DigestionScribeReceipt(
                        entry.Coverage[0].Gid,
                        record.DefinitionSha256,
                        record.EmissionSha256),
                ],
            },
        });
    }

    private static void SetStatus(
        ScribeSeedFixture fixture,
        DigestionMigrationState migration,
        DigestionTruthState truth) =>
        fixture.Document = ScribeSeedFixture.Map(fixture.Document, entry => entry with
        {
            ProjectedStatus = new DigestionStatus(migration, truth),
        });

    private static void SetWaiver(ScribeSeedFixture fixture)
    {
        var documentGid = ScribeEmissionAttestation.DocumentGid(fixture.First.Coverage[0].Gid);
        fixture.Files[documentGid + ".lean"] = fixture.Files[documentGid + ".lean"].Replace(
            "mirror-B: D5/B/" + documentGid[3..],
            "mirror-B: none(waiver:synthetic invariant)",
            StringComparison.Ordinal);
    }

    private static BackfillInventoryDocument Combine(IReadOnlyList<ScribeSeedFixture> fixtures)
    {
        var primary = fixtures[0];
        foreach (var fixture in fixtures.Skip(1))
        {
            foreach (var file in fixture.Files)
            {
                primary.Files[file.Key] = file.Value;
            }
        }

        var source = Assert.Single(primary.Document.RequireDigestionSources());
        return primary.Document.WithDigestionSources(
        [
            source with
            {
                Entries = fixtures
                    .SelectMany(static fixture => fixture.Document.RequireDigestionEntries())
                    .ToImmutableArray(),
            },
        ]);
    }

    private static LeanAxiomReport CombineReports(IEnumerable<ScribeSeedFixture> fixtures)
    {
        var reports = new Dictionary<string, LeanFileReport>(StringComparer.Ordinal);
        foreach (var fixture in fixtures)
        {
            foreach (var report in fixture.Inputs.Report.Files)
            {
                reports[report.Key.Value] = report.Value;
            }
        }

        return LeanAxiomReport.Create(reports);
    }

    private static VerifiedScribeEmissions CombineEmissions(
        IEnumerable<ScribeSeedFixture> fixtures)
    {
        var records = new List<ScribeEmissionRecord>();
        var declarationReferences = new List<string>();
        foreach (var fixture in fixtures)
        {
            var gid = fixture.First.Coverage[0].Gid;
            var documentGid = ScribeEmissionAttestation.DocumentGid(gid);
            Assert.True(fixture.Verified.TryGet(documentGid, out var record));
            records.Add(record);
            declarationReferences.Add(gid);
        }

        return VerifiedScribeEmissions.Create(records, declarationReferences);
    }

    private static RawRepositorySnapshot Raw(
        ScribeSeedFixture fixture,
        BackfillInventoryDocument document) => fixture.Raw(document);

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;
}
