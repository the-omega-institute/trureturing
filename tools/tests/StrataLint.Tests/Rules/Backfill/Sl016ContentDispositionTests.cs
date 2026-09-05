using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class Sl016ContentDispositionTests
{
    private const string SourceId = "synthetic-source";
    private const string SourcePath = "docs/develop/theory/SYNTHETIC.md";
    private const string EnginePath = "tools/StrataLint.Engine/Digestion/AtomizerRegistry.cs";

    [Fact]
    public void UnknownContentKindInScopeEmitsBlockingSl016Finding()
    {
        var fixture = CreateFixture(baselineContainsAtom: false);
        var calls = 0;

        var findings = Evaluate(fixture, "future-kind", () => calls++);

        var finding = Assert.Single(findings, item => item.Message.Contains(
            "has no disposition",
            StringComparison.Ordinal));
        Assert.Equal(1, calls);
        Assert.Equal(
            $"content kind 'future-kind' has no disposition (atom {fixture.Entry.AtomId}, "
                + $"source {SourceId})",
            finding.Message);
        Assert.Equal(AdmissionEffect.Block, finding.Effect);
    }

    [Fact]
    public void KnownContentKindInScopeEmitsNoDispositionFinding()
    {
        var fixture = CreateFixture(baselineContainsAtom: false);
        var calls = 0;

        var findings = Evaluate(fixture, "theorem", () => calls++);

        Assert.Equal(1, calls);
        Assert.DoesNotContain(findings, static item => item.Message.Contains(
            "has no disposition",
            StringComparison.Ordinal));
    }

    [Fact]
    public void UnchangedBaselineAtomIsNotReevaluatedForUnrelatedChange()
    {
        var fixture = CreateFixture(baselineContainsAtom: true);
        var calls = 0;

        var findings = Evaluate(fixture, "future-kind", () => calls++);

        Assert.Equal(0, calls);
        Assert.DoesNotContain(findings, static item => item.Message.Contains(
            "has no disposition",
            StringComparison.Ordinal));
    }

    private static ImmutableArray<RuleFinding> Evaluate(
        DispositionFixture fixture,
        string kind,
        Action onAtomize)
    {
        var policy = RegistryLoadAssert.Accepted(RegistryLoader.Load(
            Encoding.UTF8.GetBytes(TestRegistry.Canonical),
            Encoding.UTF8.GetBytes(TestRegistry.Domains))).Policy;
        var lean = AcceptedLeanClosure.Create(LeanAxiomReport.Create(
            new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)));
        return BackfillInventoryRule.EvaluateDocument(
            new BackfillInventoryValidationContext(
                fixture.Current,
                fixture.Baseline,
                policy,
                lean,
                null,
                fixture.Changes,
                CasChanges: fixture.Changes,
                ProjectedStatusChanges: fixture.Changes,
                ContentKindAtomizerResolver: _ => (_, _, contentKinds) =>
                {
                    onAtomize();
                    contentKinds![fixture.Atom.Fingerprints.RawSha256] = kind;
                    return fixture.Atomized;
                }),
            fixture.Document);
    }

    private static DispositionFixture CreateFixture(bool baselineContainsAtom)
    {
        var bytes = ImmutableArray.CreateRange(Encoding.UTF8.GetBytes("synthetic claim\n"));
        var atom = new DigestionAtom(
            0,
            bytes.Length,
            bytes,
            DigestionFingerprint.Compute(bytes.AsSpan()),
            []);
        var entry = new DigestionLedgerEntry(
            SourceId,
            SourcePath,
            AtomizerRegistry.GenericId,
            atom.Fingerprints.RawSha256["sha256:".Length..],
            atom.Fingerprints,
            [],
            new DigestionReceipts([], [], [], null),
            new DigestionStatus(DigestionMigrationState.Residual, DigestionTruthState.Open),
            atom.Fingerprints.RawSha256);
        var source = new DigestionLedgerSource(
            SourceId,
            SourcePath,
            AtomizerRegistry.GenericId,
            [],
            GenreRegistryProjection.Available(GenreRegistryCheck.NoGenreRegistry),
            [entry]);
        var document = BackfillInventoryDocument.Create([source], []);
        var baselineSource = source with { Entries = baselineContainsAtom ? [entry] : [] };
        var baselineDocument = BackfillInventoryDocument.Create([baselineSource], []);
        var current = Snapshot(document, atom, "same", includeUnrelatedCandidate: true);
        var baseline = Snapshot(
            baselineDocument,
            atom,
            "same",
            includeUnrelatedCandidate: false);
        var entryPath = EntryPath(entry);
        var changes = baselineContainsAtom
            ? RawChangeSet.Create(["README.md"])
            : RawChangeSet.CreateWithKinds([(entryPath, RawChangeKind.Added)]);
        var atomized = new AtomizedTheoryDocument(
            [atom],
            [new DigestionSlice(true, atom.RawBytes)],
            GenreRegistryCheck.NoGenreRegistry);
        return new DispositionFixture(
            document,
            entry,
            atom,
            atomized,
            current,
            baseline,
            changes);
    }

    private static RepositorySnapshot Snapshot(
        BackfillInventoryDocument document,
        DigestionAtom atom,
        string engineText,
        bool includeUnrelatedCandidate)
    {
        var source = Assert.Single(document.RequireDigestionSources());
        var entries = new List<RawRepositoryEntry>
        {
            RawRepositoryEntry.FromText(SourcePath, Encoding.UTF8.GetString(atom.RawBytes.AsSpan())),
            RawRepositoryEntry.FromText(TheoryAtomizerDataLoader.DataPath, TheoryAtomizerDataTests.Minimal),
            RawRepositoryEntry.FromText(EnginePath, engineText),
            new(
                BackfillInventoryLoader.RootPath + SourceId + "/source.toml",
                BackfillInventoryWriter.WriteSourceMetadata(source)),
        };
        foreach (var ledgerEntry in source.Entries)
        {
            entries.Add(new RawRepositoryEntry(
                DigestionCasStore.RootPath + ledgerEntry.CasRef["sha256:".Length..],
                atom.RawBytes));
            entries.Add(new RawRepositoryEntry(
                EntryPath(ledgerEntry),
                BackfillInventoryWriter.WriteAtom(ledgerEntry)));
        }

        entries.Add(RawRepositoryEntry.FromText(
            "README.md",
            includeUnrelatedCandidate ? "candidate\n" : "baseline\n"));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(RawRepositorySnapshot.Create(entries))).Snapshot;
    }

    private static string EntryPath(DigestionLedgerEntry entry) =>
        BackfillInventoryLoader.RootPath
        + entry.SourceId
        + "/residual-open/"
        + entry.AtomId
        + ".yaml";

    private sealed record DispositionFixture(
        BackfillInventoryDocument Document,
        DigestionLedgerEntry Entry,
        DigestionAtom Atom,
        AtomizedTheoryDocument Atomized,
        RepositorySnapshot Current,
        RepositorySnapshot Baseline,
        RawChangeSet Changes);
}
