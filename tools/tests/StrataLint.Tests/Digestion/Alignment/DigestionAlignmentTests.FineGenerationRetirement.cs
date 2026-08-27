using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DigestionAlignmentTests
{
    [Fact]
    public void DispositionDoesNotChangeSourceRevisionAdmissionOrRetirement()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes, DigestionTestSupport.Rules).Claims);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var baseline = Ledger([], CasEntry("old-receipt", oldAtom, oldCapture.Reference));
        var plan = DigestionIngestor.Plan(
            baseline,
            Snapshot(currentBytes, [oldCapture]),
            baseline);
        var source = Assert.Single(plan.Document.RequireDigestionSources());
        var dispositioned = plan.Document.WithDigestionSources(
        [
            source with
            {
                Entries = source.Entries.Select(entry => entry.AtomId == "old-receipt"
                    ? entry with
                    {
                        Receipts = entry.Receipts with
                        {
                            CoverDisposition = new DigestionCoverDisposition(
                                new DigestionStatus(
                                    DigestionMigrationState.Partial,
                                    DigestionTruthState.Closed),
                                ["D5/S0/Synthetic/Receipt.old_generation"],
                                [new DigestionDispositionGap(
                                    "unresolved-subitem",
                                    "remaining theorem clause")],
                                new DateTimeOffset(2026, 8, 25, 4, 3, 2, TestBudgets.ZeroDuration)),
                        },
                    }
                    : entry).ToImmutableArray(),
            },
        ]);
        var snapshot = Snapshot(
            currentBytes,
            plan.CasObjects.Prepend(oldCapture));
        var baselineSnapshot = Snapshot(oldBytes, [oldCapture]);
        var changes = RawChangeSet.Create(["docs/source.md"]);

        var plain = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.ChangedSet,
            plan.Document,
            snapshot,
            DigestionTestSupport.AcceptedLean(Array.Empty<string>()),
            VerifiedScribeEmissions.Empty,
            baseline,
            baselineSnapshot: baselineSnapshot,
            changes: changes);
        var withDisposition = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.ChangedSet,
            dispositioned,
            snapshot,
            DigestionTestSupport.AcceptedLean(Array.Empty<string>()),
            VerifiedScribeEmissions.Empty,
            baseline,
            baselineSnapshot: baselineSnapshot,
            changes: changes);

        Assert.Equal(
            DigestionReceiptAlignment.Stale,
            Assert.Single(
                withDisposition.Entries,
                static entry => entry.Entry.AtomId == "old-receipt").Alignment);
        Assert.Equal(
            Encoding.UTF8.GetBytes(DigestStatusCommand.RenderText(plain)),
            Encoding.UTF8.GetBytes(DigestStatusCommand.RenderText(withDisposition)));
    }

    [Fact]
    public void FineGenerationRetirementPreservesEveryOwnershipForm()
    {
        static (DigestionAtom Atom, DigestionCasObject Capture) Generation(string body)
        {
            var bytes = Encoding.UTF8.GetBytes($"# GICT\n\n**定理 1.1(A)**。{body}。\n");
            var atom = Assert.Single(GictAtomizer.Atomize(bytes, DigestionTestSupport.Rules).Claims);
            return (atom, DigestionCasStore.Capture(atom.RawBytes.AsSpan()));
        }

        var unowned = Generation("unowned-old");
        var covered = Generation("covered-old");
        var receipted = Generation("receipted-old");
        var formalized = Generation("formalized-old");
        var frozen = Generation("frozen-old");
        var currentBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。current。\n");
        var loaded = Ledger(
            [],
            CasEntry("unowned-receipt", unowned.Atom, unowned.Capture.Reference),
            CasEntry("covered-receipt", covered.Atom, covered.Capture.Reference),
            CasEntry("coverage-receipt", receipted.Atom, receipted.Capture.Reference),
            CasEntry("formalized-receipt", formalized.Atom, formalized.Capture.Reference),
            CasEntry("frozen-receipt", frozen.Atom, frozen.Capture.Reference));
        var source = Assert.Single(loaded.RequireDigestionSources());
        const string gid = "D5/S0/Synthetic/Receipt.owned_generation";
        var candidate = loaded.WithDigestionSources(
        [
            source with
            {
                Entries = source.Entries.Select(entry => entry.AtomId switch
                {
                    "covered-receipt" => entry with
                    {
                        CoverageGids = [gid],
                    },
                    "coverage-receipt" => entry with
                    {
                        Receipts = entry.Receipts with
                        {
                            Coverage =
                            [
                                new DigestionCoverageReceipt(
                                    gid,
                                    entry.Fingerprints.RawSha256,
                                    entry.Fingerprints.RawSha256),
                            ],
                        },
                    },
                    _ => entry,
                }).ToImmutableArray(),
            },
        ]);
        var formalizationBytes = DigestionFormalizationReceipt.Write(
            new DigestionFormalizationReceipt(
                "formalized-receipt",
                gid,
                new DigestionFormalizationSignature("owned_generation", "theorem", "True"),
                formalized.Capture.Reference,
                formalized.Atom.Fingerprints.RawSha256));
        var formalizationPath = DigestionFormalizationReceipt.RootPath
            + "formalized-receipt"
            + DigestionFormalizationReceipt.PathSuffix;
        var frozenPath = FrozenLedgerChangeClassifier.AcceptedRoot
            + "/0000000000000000000000000000000000000000000000000000000000000000.json";
        RawRepositoryEntry[] ownershipArtifacts =
        [
            new RawRepositoryEntry(formalizationPath, formalizationBytes),
            RawRepositoryEntry.FromText(frozenPath, "{\"atom_id\":\"frozen-receipt\"}\n"),
        ];
        DigestionCasObject[] historicalCaptures =
        [
            unowned.Capture,
            covered.Capture,
            receipted.Capture,
            formalized.Capture,
            frozen.Capture,
        ];
        var snapshot = Snapshot(
            currentBytes,
            historicalCaptures,
            extraEntries: ownershipArtifacts);

        var first = DigestionIngestor.Plan(candidate, snapshot, loaded);
        var plannedSource = Assert.Single(first.Document.RequireDigestionSources());

        Assert.Equal(5, first.StaleAcknowledged);
        Assert.Equal(
            [
                "coverage-receipt",
                "covered-receipt",
                "formalized-receipt",
                "frozen-receipt",
                "unowned-receipt",
            ],
            plannedSource.AcknowledgedStale.ToArray());
        Assert.Equal(1, first.ResidualOpenAdded);

        var firstBytes = DirectoryLedgerTestSupport.Image(first.Document);
        using var temporary = new TemporaryDirectory();
        var persisted = new Dictionary<string, string>(StringComparer.Ordinal);
        DirectoryLedgerTestSupport.ReplaceWithProjection(persisted, first.Document);
        DirectoryLedgerTestSupport.Write(temporary.Path, persisted);
        var settled = BackfillInventoryLoader.LoadRoot(temporary.Path);
        var secondSnapshot = Snapshot(
            currentBytes,
            historicalCaptures.Concat(first.CasObjects),
            extraEntries: ownershipArtifacts);
        var second = DigestionIngestor.Plan(
            settled,
            secondSnapshot,
            settled);
        var secondBytes = DirectoryLedgerTestSupport.Image(second.Document);

        Assert.Equal(
            [
                "coverage-receipt",
                "covered-receipt",
                "formalized-receipt",
                "frozen-receipt",
                "unowned-receipt",
            ],
            Assert.Single(second.Document.RequireDigestionSources()).AcknowledgedStale.ToArray());
        Assert.Equal(0, second.StaleAcknowledged);
        Assert.Equal(0, second.ResidualOpenAdded);
        Assert.Equal(firstBytes, secondBytes);
    }

    [Fact]
    public void IngestPreservesFineGenerationRetirementAcknowledgment()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes, DigestionTestSupport.Rules).Claims);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var baseline = Ledger([], Entry("old-receipt", oldAtom));
        var acknowledged = Ledger(
            ["old-receipt"],
            Entry("old-receipt", oldAtom));

        var plan = DigestionIngestor.Plan(
            acknowledged,
            Snapshot(currentBytes, [oldCapture]),
            baseline);

        Assert.Equal(0, plan.StaleAcknowledged);
        Assert.Equal(
            ["old-receipt"],
            Assert.Single(plan.Document.RequireDigestionSources()).AcknowledgedStale.ToArray());
    }
}
