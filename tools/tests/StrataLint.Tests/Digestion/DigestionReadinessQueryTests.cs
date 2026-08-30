using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class DigestionReadinessQueryTests
{
    private const string ReadyGid = "D5/S0/Synthetic/Readiness.ready";

    [Fact]
    public void CurrentReceiptAndScribeLeafSelectsCoverNow()
    {
        var entry = Entry("source", "ready", "theorem/1");

        var result = Classify([entry], receipts: [Receipt(entry)]);

        var record = Assert.Single(result);
        Assert.Equal("cover-now", record.Action);
        Assert.Equal(
            [
                "cover-atom:frozen-statement-resolution",
                "cover-atom:baseline-precommitment-ownership",
            ],
            record.UnknownPredicates.ToArray());
    }

    [Fact]
    public void ReceiptWithoutScribeSelectsRepairScribe()
    {
        var entry = Entry("source", "repair", "theorem/2");

        var result = Classify(
            [entry],
            receipts: [Receipt(entry)],
            scribeEmissions: VerifiedScribeEmissions.Empty);

        var record = Assert.Single(result);
        Assert.Equal("repair-scribe", record.Action);
        Assert.Contains("scribe-emission-missing:" + ReadyGid, record.OrderedBlockers);
    }

    [Fact]
    public void ReceiptWhoseScribeEmissionDoesNotReferenceDeclarationSelectsRepairScribe()
    {
        var entry = Entry("source", "missing-reference", "theorem/2-reference");

        var result = Classify(
            [entry],
            receipts: [Receipt(entry)],
            scribeEmissions: ReadyScribe(referencesDeclaration: false));

        var record = Assert.Single(result);
        Assert.Equal("repair-scribe", record.Action);
        Assert.Equal(
            ["scribe-declaration-reference-missing:" + ReadyGid],
            record.OrderedBlockers.ToArray());
        Assert.DoesNotContain(
            "scribe-emission-missing:" + ReadyGid,
            record.OrderedBlockers);
    }

    [Fact]
    public void ReceiptWithNonDeclarationGidSelectsRepairScribeWithUnknownPredicate()
    {
        const string invalidGid = "not-a-declaration-gid";
        var entry = Entry("source", "invalid-gid", "theorem/2-invalid-gid");

        var result = Classify(
            [entry],
            receipts: [Receipt(entry, invalidGid)]);

        var record = Assert.Single(result);
        Assert.Equal("repair-scribe", record.Action);
        Assert.Equal(["scribe-readiness-unknown:" + invalidGid], record.OrderedBlockers.ToArray());
        Assert.Equal(
            ["scribe-readiness:formalization-gid-not-declaration"],
            record.UnknownPredicates.ToArray());
    }

    [Fact]
    public void NoReceiptFormalizableLeafSelectsDeposit()
    {
        var result = Classify([Entry("source", "deposit", "lemma/3")]);

        var record = Assert.Single(result);
        Assert.Equal("deposit", record.Action);
        Assert.Equal(["formalization-receipt-missing"], record.OrderedBlockers.ToArray());
    }

    [Fact]
    public void ContainerWithOpenChildSelectsCloseChain()
    {
        var child = Entry("source", "child", "lemma/4");
        var parent = Entry(
            "source",
            "parent",
            "theorem/4",
            chainAtoms: [child.Entry.AtomId],
            gaps:
            [
                new DigestionGap(
                    "chain-migration-incomplete",
                    child.Entry.AtomId,
                    DigestionGapSeverity.NonFatal),
            ]);

        var record = Assert.Single(Classify([parent, child]), item => item.AtomId == "parent");

        Assert.Equal("close-chain", record.Action);
        Assert.Equal(["child"], record.OrderedBlockers.ToArray());
    }

    [Fact]
    public void AcknowledgedStaleSelectsRefreshStaleEvenWhenOtherwiseCoverable()
    {
        var entry = Entry("source", "stale", "theorem/5");

        var result = Classify(
            [entry],
            receipts: [Receipt(entry)],
            acknowledgedStale: [entry.Entry.AtomId]);

        Assert.Equal("refresh-stale", Assert.Single(result).Action);
    }

    [Fact]
    public void UnsupportedAstKindSelectsNeedsRoutingAndIsNotOmitted()
    {
        var result = Classify([Entry("source", "definition", "definition/6")]);

        var record = Assert.Single(result);
        Assert.Equal("definition", record.AtomId);
        Assert.Equal("needs-routing", record.Action);
    }

    [Theory]
    [InlineData("row")]
    [InlineData("v")]
    [InlineData("research-queue")]
    [InlineData("metadata")]
    [InlineData("negative-register")]
    [InlineData("M")]
    public void StructuralNonAssertionKindSelectsNotFormalizable(string kind)
    {
        var result = Classify([Entry("source", "not-formalizable-" + kind, kind + "/6")]);

        var record = Assert.Single(result);
        Assert.Equal("not-formalizable", record.Action);
        Assert.Equal(["non-assertion-ast-kind:" + kind], record.OrderedBlockers.ToArray());
    }

    [Fact]
    public void FormalizableKindIsNeverClassifiedAsNotFormalizable()
    {
        var record = Assert.Single(Classify([Entry("source", "assertion", "theorem/6-assertion")]));

        Assert.NotEqual("not-formalizable", record.Action);
    }

    [Fact]
    public void NotFormalizableKindAlphabetIsExactlyTheMeasuredStructuralKinds()
    {
        Assert.Equal(
            ["row", "v", "research-queue", "metadata", "negative-register", "M"],
            DigestionAstKindPolicy.NotFormalizableKinds.ToArray());
    }

    [Fact]
    public void GidUsedByAnotherAtomDoesNotBlockCoverNow()
    {
        var target = Entry("source", "target", "theorem/7");
        var other = Entry(
            "source",
            "other",
            "theorem/8",
            migration: DigestionMigrationState.Absorbed,
            truth: DigestionTruthState.Closed,
            coverageGids: [ReadyGid]);

        var result = Classify([target, other], receipts: [Receipt(target)]);

        Assert.Equal("cover-now", Assert.Single(result).Action);
    }

    [Fact]
    public void EveryResidualOpenEntryAppearsExactlyOnce()
    {
        var first = Entry("source-b", "atom-b", "definition/9");
        var second = Entry("source-a", "atom-a", "lemma/10");
        var nonResidual = Entry(
            "source-a",
            "closed",
            "theorem/11",
            migration: DigestionMigrationState.Absorbed,
            truth: DigestionTruthState.Closed);

        var result = Classify([first, second, nonResidual]);

        Assert.Equal(2, result.Length);
        Assert.Equal(2, result.Select(static item => (item.SourceId, item.AtomId)).Distinct().Count());
        Assert.Contains(result, static item => item.AtomId == "atom-a");
        Assert.Contains(result, static item => item.AtomId == "atom-b");
    }

    [Fact]
    public void SelectorRequiresResidualAndOpenIndependently()
    {
        var included = Entry("source", "residual-open", "theorem/selector-included");
        var nonOpen = Entry(
            "source",
            "residual-closed",
            "theorem/selector-non-open",
            migration: DigestionMigrationState.Residual,
            truth: DigestionTruthState.Closed);
        var nonResidual = Entry(
            "source",
            "partial-open",
            "theorem/selector-non-residual",
            migration: DigestionMigrationState.Partial,
            truth: DigestionTruthState.Open);

        var result = Classify([nonOpen, included, nonResidual]);

        Assert.Equal(["residual-open"], result.Select(static item => item.AtomId));
    }

    [Fact]
    public void PresentReceiptAtomIdsInputDistinguishesStaleReceiptFromMissingReceipt()
    {
        var entry = Entry("source", "present-receipt", "theorem/present-receipt");
        var result = DigestionReadinessQuery.Classify(
            Document([entry]),
            Evaluation([entry]),
            new Dictionary<string, DigestionFormalizationReceipt>(StringComparer.Ordinal),
            ImmutableHashSet.Create(StringComparer.Ordinal, entry.Entry.AtomId),
            ReadyScribe());

        var record = Assert.Single(result);
        Assert.Equal("deposit", record.Action);
        Assert.Equal(["formalization-receipt-stale"], record.OrderedBlockers.ToArray());
    }

    [Fact]
    public void OrderingIsDeterministicAndEmitsNoNumericScore()
    {
        var deposit = Entry("source-z", "deposit", "theorem/12");
        var routing = Entry("source-a", "routing", "definition/13");
        var quarantine = Entry(
            "source-z",
            "quarantine",
            "definition/14",
            quarantine: new DigestionQuarantine("blocked", "re-enter", "missing-prerequisite"));
        var evaluation = Evaluation([deposit, routing, quarantine]);
        var document = Document([deposit, routing, quarantine]);
        var first = DigestionReadinessQuery.Classify(
            document,
            evaluation,
            new Dictionary<string, DigestionFormalizationReceipt>(StringComparer.Ordinal),
            ImmutableHashSet<string>.Empty,
            ReadyScribe());
        var second = DigestionReadinessQuery.Classify(
            document,
            evaluation,
            new Dictionary<string, DigestionFormalizationReceipt>(StringComparer.Ordinal),
            ImmutableHashSet<string>.Empty,
            ReadyScribe());

        var firstJson = DigestStatusCommand.RenderReadiness(first);
        var secondJson = DigestStatusCommand.RenderReadiness(second);

        Assert.Equal(firstJson, secondJson);
        using var json = JsonDocument.Parse(firstJson);
        Assert.Equal(
            ["quarantine", "routing", "deposit"],
            json.RootElement.GetProperty("entries")
                .EnumerateArray()
                .Select(static item => item.GetProperty("atom_id").GetString()));
        Assert.DoesNotContain("score", firstJson, StringComparison.OrdinalIgnoreCase);
        Assert.DoesNotContain("rank", firstJson, StringComparison.OrdinalIgnoreCase);
        Assert.DoesNotContain("roi", firstJson, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void SameActionOrderingUsesSourceIdThenAtomId()
    {
        var result = Classify(
        [
            Entry("source-b", "atom-a", "theorem/12-b-a"),
            Entry("source-a", "atom-z", "theorem/12-a-z"),
            Entry("source-a", "atom-a", "theorem/12-a-a"),
        ]);

        Assert.Equal(
            ["source-a/atom-a", "source-a/atom-z", "source-b/atom-a"],
            result.Select(static item => item.SourceId + "/" + item.AtomId));
        Assert.All(result, static item => Assert.Equal("deposit", item.Action));
    }

    [Fact]
    public void QuarantinedAndWithheldEntriesAppearWithTheirOwnAction()
    {
        var quarantined = Entry(
            "source",
            "quarantined",
            "theorem/15",
            quarantine: new DigestionQuarantine("blocked", "re-enter", "missing-prerequisite"));
        var withheld = Entry(
            "source",
            "withheld",
            "theorem/16",
            coverDisposition: new DigestionCoverDisposition(
                new DigestionStatus(DigestionMigrationState.Partial, DigestionTruthState.Closed),
                [ReadyGid],
                [new DigestionDispositionGap("unresolved-subitem", "remaining")],
                new DateTimeOffset(2026, 8, 30, 0, 0, 0, TestBudgets.ZeroDuration)));

        var result = Classify([withheld, quarantined]);

        Assert.Equal("quarantined", result[0].Action);
        Assert.Equal("withheld", result[1].Action);
    }

    private static ImmutableArray<DigestionReadinessRecord> Classify(
        ImmutableArray<DigestionEntryEvaluation> entries,
        ImmutableArray<DigestionFormalizationReceipt> receipts = default,
        VerifiedScribeEmissions? scribeEmissions = null,
        ImmutableArray<string> acknowledgedStale = default)
    {
        var receiptMap = (receipts.IsDefault ? [] : receipts)
            .ToDictionary(static item => item.AtomId, StringComparer.Ordinal);
        return DigestionReadinessQuery.Classify(
            Document(entries, acknowledgedStale),
            Evaluation(entries),
            receiptMap,
            receiptMap.Keys.ToImmutableHashSet(StringComparer.Ordinal),
            scribeEmissions ?? ReadyScribe());
    }

    private static DigestionLedgerEvaluation Evaluation(
        ImmutableArray<DigestionEntryEvaluation> entries) => new(entries, []);

    private static BackfillInventoryDocument Document(
        ImmutableArray<DigestionEntryEvaluation> entries,
        ImmutableArray<string> acknowledgedStale = default) =>
        BackfillInventoryDocument.Create(
            entries
                .GroupBy(static item => item.Entry.SourceId, StringComparer.Ordinal)
                .Select(group => new DigestionLedgerSource(
                    group.Key,
                    "synthetic/" + group.Key + ".md",
                    AtomizerRegistry.GenericId,
                    acknowledgedStale.IsDefault
                        ? []
                        : acknowledgedStale.Where(id => group.Any(item => item.Entry.AtomId == id))
                            .ToImmutableArray(),
                    GenreRegistryProjection.Available(GenreRegistryCheck.NoGenreRegistry),
                    group.Select(static item => item.Entry).ToImmutableArray()))
                .ToImmutableArray(),
            []);

    private static DigestionEntryEvaluation Entry(
        string sourceId,
        string atomId,
        string astPath,
        DigestionMigrationState migration = DigestionMigrationState.Residual,
        DigestionTruthState truth = DigestionTruthState.Open,
        ImmutableArray<string> coverageGids = default,
        ImmutableArray<string> chainAtoms = default,
        ImmutableArray<DigestionGap> gaps = default,
        DigestionQuarantine? quarantine = null,
        DigestionCoverDisposition? coverDisposition = null)
    {
        var fingerprints = new DigestionFingerprints(
            "sha256:" + new string('a', 64),
            "sha256:" + new string('b', 64));
        var entry = new DigestionLedgerEntry(
            sourceId,
            "synthetic/" + sourceId + ".md",
            AtomizerRegistry.GenericId,
            atomId,
            astPath,
            null,
            fingerprints,
            coverageGids.IsDefault ? [] : coverageGids,
            new DigestionReceipts(
                [],
                [],
                [],
                chainAtoms.IsDefault ? [] : chainAtoms,
                null,
                quarantine,
                coverDisposition),
            new DigestionStatus(migration, truth),
            fingerprints.RawSha256);
        return new DigestionEntryEvaluation(
            entry,
            DigestionReceiptAlignment.Seen,
            new DigestionStatus(migration, truth),
            false,
            gaps.IsDefault ? [] : gaps);
    }

    private static DigestionFormalizationReceipt Receipt(
        DigestionEntryEvaluation entry,
        string gid = ReadyGid) => new(
        entry.Entry.AtomId,
        gid,
        new DigestionFormalizationSignature("ready", "theorem", "True"),
        entry.Entry.CasRef,
        entry.Entry.Fingerprints.RawSha256);

    private static VerifiedScribeEmissions ReadyScribe(bool referencesDeclaration = true)
    {
        var documentGid = ScribeEmissionAttestation.DocumentGid(ReadyGid);
        return VerifiedScribeEmissions.Create(
            [
                new ScribeEmissionRecord(
                    documentGid,
                    ScribeEmissionAttestation.DefinitionPath(documentGid),
                    "sha256:" + new string('c', 64),
                    ScribeEmissionAttestation.EmissionPath(documentGid),
                    "sha256:" + new string('d', 64)),
            ],
            referencesDeclaration ? [ReadyGid] : []);
    }
}
