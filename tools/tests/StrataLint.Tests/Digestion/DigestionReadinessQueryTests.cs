using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class DigestionReadinessQueryTests
{
    private const string ReadyGid = "D5/S0/Synthetic/Readiness.ready";

    private const string UnreadyGid = "D5/S0/Synthetic/Readiness.unready";

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
            DigestionContentKindPolicy.NotFormalizableKinds.ToArray());
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
            Kinds([entry]),
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
            Kinds([deposit, routing, quarantine]),
            new Dictionary<string, DigestionFormalizationReceipt>(StringComparer.Ordinal),
            ImmutableHashSet<string>.Empty,
            ReadyScribe());
        var second = DigestionReadinessQuery.Classify(
            document,
            evaluation,
            Kinds([deposit, routing, quarantine]),
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

    // 第三轮评审(architecture/quality/tests 三席独立)实测:只改 ActionPriorities 中的一个常数
    // (如 cover-now 6->9)即可让 972 条可直接 cover 的工作排到 repair-scribe/deposit 之后,
    // 而定向 81/81 全绿、零具名红 —— 即整张 action 优先级表当时无任何测试守着。
    // 故断言**完整序列**而非相邻两项:任何单常数退化都必须红。
    [Fact]
    public void ActionPriorityOrderIsTheFullApprovedSequence()
    {
        var stale = Entry("s", "a-stale", "theorem/1");
        var coverNow = Entry("s", "b-cover", "theorem/2");
        var repairScribe = Entry("s", "c-repair", "theorem/3");
        var deposit = Entry("s", "d-deposit", "theorem/4");
        var child = Entry("s", "e-child", "lemma/5");
        var closeChain = Entry(
            "s",
            "f-chain",
            "theorem/6",
            chainAtoms: [child.Entry.AtomId],
            gaps: [new DigestionGap("chain-migration-incomplete", child.Entry.AtomId, DigestionGapSeverity.NonFatal)]);
        var needsRouting = Entry("s", "g-routing", "definition/7");
        var notFormalizable = Entry("s", "h-terminal", "row/8");
        var quarantined = Entry(
            "s",
            "i-quarantine",
            "theorem/9",
            quarantine: new DigestionQuarantine("blocked", "re-enter", "missing-prerequisite"));
        var withheld = Entry(
            "s",
            "j-withheld",
            "theorem/10",
            coverDisposition: new DigestionCoverDisposition(
                new DigestionStatus(DigestionMigrationState.Partial, DigestionTruthState.Closed),
                [ReadyGid],
                [new DigestionDispositionGap("unresolved-subitem", "remaining")],
                new DateTimeOffset(2026, 8, 30, 0, 0, 0, TestBudgets.ZeroDuration)));

        var result = Classify(
            [deposit, coverNow, repairScribe, stale, closeChain, child, needsRouting, notFormalizable, quarantined, withheld],
            receipts: [Receipt(stale), Receipt(coverNow), Receipt(repairScribe, UnreadyGid)],
            acknowledgedStale: [stale.Entry.AtomId]);

        Assert.Equal(
            [
                "quarantined",
                "withheld",
                "refresh-stale",
                "not-formalizable",
                "needs-routing",
                "close-chain",
                "cover-now",
                "repair-scribe",
                "deposit",
            ],
            result.Select(static item => item.Action).Distinct());
    }

    // 第三轮 architecture 席实测:移除 `gap.Detail == atomId` 后定向 81/81 全绿。
    // 单 child 的夹具无判别力 —— 已闭与未闭的 child 必须同时在场,才能证明只列未闭者。
    [Fact]
    public void CloseChainBlockersNameOnlyTheUnfinishedChildren()
    {
        var openChild = Entry("source", "open-child", "lemma/20");
        var closedChild = Entry("source", "closed-child", "lemma/21");
        var parent = Entry(
            "source",
            "parent",
            "theorem/20",
            chainAtoms: [closedChild.Entry.AtomId, openChild.Entry.AtomId],
            gaps:
            [
                new DigestionGap(
                    "chain-migration-incomplete",
                    openChild.Entry.AtomId,
                    DigestionGapSeverity.NonFatal),
            ]);

        var record = Assert.Single(
            Classify([parent, openChild, closedChild]),
            item => item.AtomId == "parent");

        Assert.Equal("close-chain", record.Action);
        Assert.Equal(["open-child"], record.OrderedBlockers.ToArray());
    }

    // 第三轮 architecture/tests 两席实测:把 receipt.RegisteredGids 改为 .Take(1) 后定向 81/81 全绿,
    // 即 hosted extension 的 Scribe 就绪从未被检查。RegisteredGids = [PrimaryGid, ..HostedExtensions]。
    [Fact]
    public void HostedExtensionScribeReadinessIsNotSkipped()
    {
        var entry = Entry("source", "multi-gid", "theorem/30");
        var receipt = new DigestionFormalizationReceipt(
            entry.Entry.AtomId,
            ReadyGid,
            new DigestionFormalizationSignature("ready", "theorem", "True"),
            entry.Entry.CasRef,
            entry.Entry.Fingerprints.RawSha256,
            [new DigestionFormalizationExtension(UnreadyGid, new DigestionFormalizationSignature("unready", "theorem", "True"))]);

        var record = Assert.Single(Classify([entry], receipts: [receipt]));

        Assert.Equal("repair-scribe", record.Action);
        Assert.Contains(
            record.OrderedBlockers,
            blocker => blocker.Contains(UnreadyGid, StringComparison.Ordinal));
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
            Kinds(entries),
            receiptMap,
            receiptMap.Keys.ToImmutableHashSet(StringComparer.Ordinal),
            scribeEmissions ?? ReadyScribe());
    }

    private static DigestionLedgerEvaluation Evaluation(
        ImmutableArray<DigestionEntryEvaluation> entries) => new(entries, []);

    private static IReadOnlyDictionary<string, string> Kinds(
        ImmutableArray<DigestionEntryEvaluation> entries) =>
        entries.GroupBy(static item => item.Entry.AtomId, StringComparer.Ordinal)
            .ToDictionary(
                static group => group.Key,
                static group => Assert.Single(group.First().Atom!.Context).Text,
                StringComparer.Ordinal);

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
        string contentLocatorFixture,
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
        var separator = contentLocatorFixture.IndexOf('/', StringComparison.Ordinal);
        var contentKind = separator < 0
            ? contentLocatorFixture
            : contentLocatorFixture[..separator];
        var rawBytes = ImmutableArray.CreateRange(Encoding.UTF8.GetBytes(contentLocatorFixture));
        var entry = new DigestionLedgerEntry(
            sourceId,
            "synthetic/" + sourceId + ".md",
            AtomizerRegistry.GenericId,
            atomId,
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
            new DigestionAtom(
                0,
                rawBytes.Length,
                rawBytes,
                fingerprints,
                [new DigestionContext(0, contentKind)]),
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
