using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;
using static StrataLint.Tests.DigestionTestSupport;

namespace StrataLint.Tests;

public sealed class CoverageStatementReceiptTests
{
    private const string ModuleGid = "D5/S0/Carrier/StatementReceipt";
    private const string ModulePath = ModuleGid + ".lean";
    private const string DeclarationGid = ModuleGid + ".target";

    [Fact]
    public void ModuleGidResolutionTracksFrozenStatePin()
    {
        var firstPin = FrozenStatementReceiptTestData.Id('1');
        var secondPin = FrozenStatementReceiptTestData.Id('2');
        Assert.True(Gid.TryParse(ModuleGid, out var gid));
        var report = LeanAxiomReport.Create(
            new Dictionary<string, LeanFileReport>(StringComparer.Ordinal));

        var first = FrozenStatementIndex.Create(
            FrozenStateCatalog.Load(StateSnapshot(firstPin)),
            report);
        var second = FrozenStatementIndex.Create(
            FrozenStateCatalog.Load(StateSnapshot(secondPin)),
            report);

        Assert.True(first.TryResolve(gid, out var firstStatement, out var firstMessage), firstMessage);
        Assert.True(second.TryResolve(gid, out var secondStatement, out var secondMessage), secondMessage);
        Assert.Equal(firstPin, firstStatement!.Value);
        Assert.Equal(secondPin, secondStatement!.Value);
    }

    [Fact]
    public void DeclarationGidResolutionComesFromCurrentReportAndMissingDeclarationIsUnresolved()
    {
        var path = RepoPath.CreateKnown(ModulePath);
        var declaration = new LeanDeclaration(
            "D5.S0.Carrier.StatementReceipt.target",
            "theorem",
            "True",
            ImmutableArray<string>.Empty)
        {
            NameKey = "ns(n0,6:target)",
        };
        var fileReport = new LeanFileReport([], [declaration]);
        var report = LeanAxiomReport.Create(
            new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)
            {
                [ModulePath] = fileReport,
            });
        var expected = Assert.Single(
            CanonicalStatementWriter.DeclarationStatementIds(path, fileReport)).StatementId;
        var state = FrozenStateCatalog.Load(StateSnapshot(FrozenStatementReceiptTestData.Id('1')));
        Assert.True(Gid.TryParse(DeclarationGid, out var gid));

        var present = FrozenStatementIndex.Create(state, report);
        var missing = FrozenStatementIndex.Create(
            state,
            LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>(StringComparer.Ordinal)));

        Assert.True(present.TryResolve(gid, out var statementId, out var message), message);
        Assert.Equal(expected, statementId);
        Assert.False(missing.TryResolve(gid, out var missingStatementId, out var missingMessage));
        Assert.Null(missingStatementId);
        Assert.Contains("0 current report declarations", missingMessage, StringComparison.Ordinal);
    }

    [Fact]
    public void RepositoryCoverageEdgesMatchResolvableFrozenStatementsOrCarryNull()
    {
        const string unresolvedGid = "D5/S0/Carrier/Missing.target";
        var targetStatementId = FrozenStatementReceiptTestData.Id('6');
        var fingerprints = new DigestionFingerprints(
            "sha256:" + new string('a', 64),
            "sha256:" + new string('b', 64));
        var entry = new DigestionLedgerEntry(
            "source",
            "docs/source.md",
            AtomizerRegistry.NoAtomizerId,
            new string('a', 64),
            fingerprints,
            [
                new DigestionCoverageEdge(DeclarationGid, targetStatementId),
                new DigestionCoverageEdge(unresolvedGid, null),
            ],
            new DigestionReceipts([], [], [], null),
            new DigestionStatus(DigestionMigrationState.Partial, DigestionTruthState.Closed),
            fingerprints.RawSha256);
        var document = Document(AtomizerRegistry.NoAtomizerId, [entry]);
        var source = Assert.Single(document.RequireDigestionSources());
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [$"{BackfillInventoryLoader.RootPath}source/source.toml"] = Encoding.UTF8.GetString(
                BackfillInventoryWriter.WriteSourceMetadata(source).AsSpan()),
            [$"{BackfillInventoryLoader.RootPath}source/partial-closed/{entry.AtomId}.yaml"] =
                Encoding.UTF8.GetString(BackfillInventoryWriter.WriteAtom(entry).AsSpan()),
            [ModulePath] = TargetSource("by trivial"),
        };
        FrozenStatementReceiptTestData.AddLedger(
            files,
            new FrozenStatementReceiptTestData.Module(
                ModulePath,
                FrozenStatementReceiptTestData.Id('2'),
                [new FrozenStatementReceiptTestData.Declaration("target", targetStatementId)]));
        var raw = RawRepositorySnapshot.Create(files.Select(static item =>
            RawRepositoryEntry.FromText(item.Key, item.Value)));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(raw)).Snapshot;
        var frozenStatements = FrozenStatementReceiptTestData.Index(snapshot);
        var mismatches = BackfillInventoryLoader.Load(snapshot)
            .RequireDigestionEntries()
            .SelectMany(static entry => entry.Coverage.Select(receipt =>
                (entry.AtomId, Receipt: receipt)))
            .Select(item =>
            {
                if (!Gid.TryParse(item.Receipt.Gid, out var gid))
                {
                    return $"{item.AtomId}:{item.Receipt.Gid}:invalid-gid";
                }

                if (!frozenStatements.TryResolve(gid, out var statementId, out _))
                {
                    return item.Receipt.TargetStatementId is null
                        ? null
                        : $"{item.AtomId}:{item.Receipt.Gid}:unresolved target must be null:"
                            + item.Receipt.TargetStatementId;
                }

                return item.Receipt.TargetStatementId == statementId!.Value
                    ? null
                    : $"{item.AtomId}:{item.Receipt.Gid}:expected={statementId.Value}:"
                        + $"actual={item.Receipt.TargetStatementId}";
            })
            .Where(static mismatch => mismatch is not null)
            .ToArray();

        Assert.True(mismatches.Length == 0, string.Join(Environment.NewLine, mismatches));
    }

    [Fact]
    public void ProofBodyChangeBreaksOldByteBindingButKeepsStatementReceiptValid()
    {
        var before = TargetSource("by trivial");
        var after = TargetSource("by exact True.intro");
        var statementId = DigestionFingerprint.Compute(Encoding.UTF8.GetBytes(before)).RawSha256;
        Assert.NotEqual(
            statementId,
            DigestionFingerprint.Compute(Encoding.UTF8.GetBytes(after)).RawSha256);

        var evaluation = Evaluate(
            DeclarationGid,
            statementId,
            statementId,
            FrozenStatementReceiptTestData.Id('2'),
            after);

        Assert.DoesNotContain(
            evaluation.Entries.Single().Gaps,
            static gap => gap.Code == "coverage-target-mismatch");
    }

    [Fact]
    public void StatementChangeStillReportsCoverageReceiptMismatch()
    {
        var targetSource = TargetSource("by trivial");
        var receiptStatementId = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes(targetSource)).RawSha256;
        var changedStatementId = FrozenStatementReceiptTestData.Id('3');
        Assert.NotEqual(receiptStatementId, changedStatementId);

        var evaluation = Evaluate(
            DeclarationGid,
            receiptStatementId,
            changedStatementId,
            FrozenStatementReceiptTestData.Id('2'),
            targetSource);

        Assert.Contains(
            evaluation.Entries.Single().Gaps,
            static gap => gap.Code == "coverage-target-mismatch");
    }

    [Fact]
    public void NullTargetForResolvableFrozenStatementDerivesPartialOpenWithoutIntegrityMismatch()
    {
        var targetSource = TargetSource("by trivial");
        var evaluation = Evaluate(
            DeclarationGid,
            receiptStatementId: null,
            FrozenStatementReceiptTestData.Id('3'),
            FrozenStatementReceiptTestData.Id('2'),
            targetSource);
        var status = Assert.Single(evaluation.Entries);

        Assert.Equal(DigestionMigrationState.Partial, status.DerivedStatus.Migration);
        Assert.Equal(DigestionTruthState.Open, status.DerivedStatus.Truth);
        Assert.DoesNotContain(
            status.Gaps,
            static gap => gap.Code == "coverage-target-mismatch");
    }

    [Fact]
    public void Sl016NullTargetForResolvableFrozenStatementKeepsTruthOpen()
    {
        var evaluation = Evaluate(
            DeclarationGid,
            receiptStatementId: null,
            FrozenStatementReceiptTestData.Id('3'),
            FrozenStatementReceiptTestData.Id('2'),
            TargetSource("by trivial"));

        Assert.Equal(
            DigestionTruthState.Open,
            Assert.Single(evaluation.Entries).DerivedStatus.Truth);
    }

    [Fact]
    public void ModuleGidUsesFrozenModuleStatementId()
    {
        var targetSource = TargetSource("by trivial");
        var moduleStatementId = DigestionFingerprint.Compute(
            Encoding.UTF8.GetBytes(targetSource)).RawSha256;
        var evaluation = Evaluate(
            ModuleGid,
            moduleStatementId,
            FrozenStatementReceiptTestData.Id('1'),
            moduleStatementId,
            targetSource);

        Assert.DoesNotContain(
            evaluation.Entries.Single().Gaps,
            static gap => gap.Code == "coverage-target-mismatch");
    }

    [Fact]
    public void FrozenLedgerChangeRechecksStatementReceipt()
    {
        var previousStatementId = FrozenStatementReceiptTestData.Id('4');
        var evaluation = Evaluate(
            DeclarationGid,
            previousStatementId,
            FrozenStatementReceiptTestData.Id('5'),
            FrozenStatementReceiptTestData.Id('2'),
            TargetSource("by trivial"),
            FrozenLedgerChangeClassifier.AcceptedRoot + "/changed.json");

        Assert.Contains(
            evaluation.Entries.Single().Gaps,
            static gap => gap.Code == "coverage-target-mismatch");
        Assert.Contains(
            evaluation.Findings,
            static finding => finding.Contains(
                "handwritten status",
                StringComparison.Ordinal));
    }

    [Fact]
    public void AmbiguousFrozenDeclarationShortNameDoesNotResolve()
    {
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [ModulePath] = TargetSource("by trivial"),
        };
        FrozenStatementReceiptTestData.AddLedger(
            files,
            new FrozenStatementReceiptTestData.Module(
                ModulePath,
                FrozenStatementReceiptTestData.Id('2'),
                [
                    new FrozenStatementReceiptTestData.Declaration(
                        "Alpha.target",
                        FrozenStatementReceiptTestData.Id('6')),
                    new FrozenStatementReceiptTestData.Declaration(
                        "Beta.target",
                        FrozenStatementReceiptTestData.Id('7')),
                ]));
        var snapshot = Snapshot(files.Select(static item =>
            (item.Key, Encoding.UTF8.GetBytes(item.Value))).ToArray());
        Assert.True(Gid.TryParse(DeclarationGid, out var gid));

        var resolved = FrozenStatementReceiptTestData.Index(snapshot).TryResolve(
            gid,
            out var statementId,
            out var message);

        Assert.False(resolved);
        Assert.Null(statementId);
        Assert.Contains("resolves to 2 current report declarations", message, StringComparison.Ordinal);
    }

    [Fact]
    public void UnfrozenHostPathDoesNotResolveStatement()
    {
        var snapshot = Snapshot(FrozenStatementReceiptTestData.LedgerFiles(
            new FrozenStatementReceiptTestData.Module(
                "D5/S0/Carrier/Other.lean",
                FrozenStatementReceiptTestData.Id('8'),
                [new FrozenStatementReceiptTestData.Declaration(
                    "target",
                    FrozenStatementReceiptTestData.Id('9'))])));
        Assert.True(Gid.TryParse(DeclarationGid, out var gid));

        var resolved = FrozenStatementReceiptTestData.Index(snapshot).TryResolve(
            gid,
            out var statementId,
            out var message);

        Assert.False(resolved);
        Assert.Null(statementId);
        Assert.Contains("host module is not a member of frozen state", message, StringComparison.Ordinal);
    }

    [Fact]
    public void NoncanonicalFrozenDeclarationNameKeyDoesNotResolve()
    {
        var snapshot = Snapshot(FrozenStatementReceiptTestData.LedgerFiles(
            new FrozenStatementReceiptTestData.Module(
                ModulePath,
                FrozenStatementReceiptTestData.Id('8'),
                [new FrozenStatementReceiptTestData.Declaration(
                    "target",
                    FrozenStatementReceiptTestData.Id('9'),
                    EncodedNameKey: "ns(ns(n0,4:1bad),6:target)")])));
        Assert.True(Gid.TryParse(DeclarationGid, out var gid));

        var resolved = FrozenStatementReceiptTestData.Index(snapshot).TryResolve(
            gid,
            out var statementId,
            out var message);

        Assert.False(resolved);
        Assert.Null(statementId);
        Assert.Contains("invalid name key", message, StringComparison.Ordinal);
    }

    [Fact]
    public void TrailingGarbageInFrozenDeclarationNameKeyDoesNotResolve()
    {
        var snapshot = Snapshot(FrozenStatementReceiptTestData.LedgerFiles(
            new FrozenStatementReceiptTestData.Module(
                ModulePath,
                FrozenStatementReceiptTestData.Id('8'),
                [
                    new FrozenStatementReceiptTestData.Declaration(
                        "other",
                        FrozenStatementReceiptTestData.Id('7'),
                        EncodedNameKey: "ns(n0,5:other)junk"),
                    new FrozenStatementReceiptTestData.Declaration(
                        "target",
                        FrozenStatementReceiptTestData.Id('9')),
                ])));
        Assert.True(Gid.TryParse(DeclarationGid, out var gid));

        var resolved = FrozenStatementReceiptTestData.Index(snapshot).TryResolve(
            gid,
            out var statementId,
            out var message);

        Assert.False(resolved);
        Assert.Null(statementId);
        Assert.Contains("invalid name key", message, StringComparison.Ordinal);
    }

    [Fact]
    public void GeneratedPrivateDeclarationDoesNotBlockCanonicalTargetResolution()
    {
        var targetStatementId = FrozenStatementReceiptTestData.Id('9');
        var snapshot = Snapshot(FrozenStatementReceiptTestData.LedgerFiles(
            new FrozenStatementReceiptTestData.Module(
                ModulePath,
                FrozenStatementReceiptTestData.Id('8'),
                [
                    new FrozenStatementReceiptTestData.Declaration(
                        "private.splitter",
                        FrozenStatementReceiptTestData.Id('7'),
                        EncodedNameKey: "ns(nn(ns(n0,8:_private),0),8:splitter)"),
                    new FrozenStatementReceiptTestData.Declaration(
                        "target",
                        targetStatementId),
                ])));
        Assert.True(Gid.TryParse(DeclarationGid, out var gid));

        var resolved = FrozenStatementReceiptTestData.Index(snapshot).TryResolve(
            gid,
            out var statementId,
            out var message);

        Assert.True(resolved, message);
        Assert.Equal(targetStatementId, statementId!.Value);
    }

    internal static DigestionLedgerEvaluation Evaluate(
        string gid,
        string? receiptStatementId,
        string targetStatementId,
        string moduleStatementId,
        string targetSource,
        string? changedPath = null)
    {
        var sourceBytes = Encoding.UTF8.GetBytes("statement receipt source\n");
        var atom = new DigestionAtom(
            0,
            sourceBytes.Length,
            ImmutableArray.CreateRange(sourceBytes),
            DigestionFingerprint.Compute(sourceBytes),
            []);
        var receipt = new DigestionCoverageEdge(
            gid,
            receiptStatementId);
        var entry = Entry(
            atom,
            "statement-receipt",
            AtomizerRegistry.NoAtomizerId,
            DigestionMigrationState.Absorbed,
            DigestionTruthState.Closed,
            [],
            new DigestionReceipts([], [], [], null)) with
        {
            Coverage = [receipt],
        };
        var document = Document(AtomizerRegistry.NoAtomizerId, [entry]);
        var files = new Dictionary<string, string>(StringComparer.Ordinal)
        {
            ["docs/source.md"] = Encoding.UTF8.GetString(sourceBytes),
            [ModulePath] = targetSource,
        };
        var cas = CasFile(atom);
        files[cas.Path] = Encoding.UTF8.GetString(cas.Bytes);
        FrozenStatementReceiptTestData.AddLedger(
            files,
            new FrozenStatementReceiptTestData.Module(
                ModulePath,
                moduleStatementId,
                [new FrozenStatementReceiptTestData.Declaration("target", targetStatementId)]));
        var snapshot = Snapshot(files.Select(static item =>
            (item.Key, Encoding.UTF8.GetBytes(item.Value))).ToArray());
        var report = new LeanFileReport(
            [],
            [new LeanDeclaration("target", "theorem", "True", [])
            {
                NameKey = "ns(n0,6:target)",
                PrecomputedStatementId = targetStatementId,
            }]);

        return DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.ChangedSet,
            document,
            snapshot,
            AcceptedLean((ModulePath, report)),
            baselineDocument: document,
            changes: RawChangeSet.Create([changedPath ?? ModulePath]));
    }

    private static RepositorySnapshot StateSnapshot(string statementId)
    {
        var statePath = FrozenStatePath.FromModulePath(RepoPath.CreateKnown(ModulePath)).Value;
        return Snapshot(
            (ModulePath, Encoding.UTF8.GetBytes(TargetSource("by trivial"))),
            (statePath, FrozenStateRecord.Encode(StatementId.Create(statementId)).ToArray()));
    }

    private static string TargetSource(string targetProof) => $$"""
        /- GID: {{ModuleGid}}
           generality: G
           mirror-B: none(waiver:test)
           mirror-E: none(waiver:test)
           anchors: []
           digest: Statement receipt fixture. -/
        theorem target : True := {{targetProof}}
        """;
}
