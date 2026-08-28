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
    public void RepositoryCoverageReceiptsBindActiveFrozenStatements()
    {
        var root = TestRepositoryLayout.FindRoot();
        var raw = GitRepositorySnapshotReader.ReadCurrent(root);
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(raw)).Snapshot;
        var frozenStatements = FrozenStatementIndex.Load(snapshot);
        var mismatches = BackfillInventoryLoader.Load(snapshot)
            .RequireDigestionEntries()
            .SelectMany(static entry => entry.Receipts.Coverage.Select(receipt =>
                (entry.AtomId, Receipt: receipt)))
            .Select(item =>
            {
                if (!Gid.TryParse(item.Receipt.Gid, out var gid))
                {
                    return $"{item.AtomId}:{item.Receipt.Gid}:invalid-gid";
                }

                if (!frozenStatements.TryResolve(gid, out var statementId, out var message))
                {
                    return $"{item.AtomId}:{item.Receipt.Gid}:{message}";
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
            static gap => gap.Code == "coverage-receipt-mismatch");
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
            static gap => gap.Code == "coverage-receipt-mismatch");
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
            static gap => gap.Code == "coverage-receipt-mismatch");
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
            static gap => gap.Code == "coverage-receipt-mismatch");
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

        var resolved = FrozenStatementIndex.Load(snapshot).TryResolve(
            gid,
            out var statementId,
            out var message);

        Assert.False(resolved);
        Assert.Null(statementId);
        Assert.Contains("resolves to 2 frozen declarations", message, StringComparison.Ordinal);
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

        var resolved = FrozenStatementIndex.Load(snapshot).TryResolve(
            gid,
            out var statementId,
            out var message);

        Assert.False(resolved);
        Assert.Null(statementId);
        Assert.Contains("host module is not active", message, StringComparison.Ordinal);
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

        var resolved = FrozenStatementIndex.Load(snapshot).TryResolve(
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

        var resolved = FrozenStatementIndex.Load(snapshot).TryResolve(
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

        var resolved = FrozenStatementIndex.Load(snapshot).TryResolve(
            gid,
            out var statementId,
            out var message);

        Assert.True(resolved, message);
        Assert.Equal(targetStatementId, statementId!.Value);
    }

    internal static DigestionLedgerEvaluation Evaluate(
        string gid,
        string receiptStatementId,
        string targetStatementId,
        string moduleStatementId,
        string targetSource,
        string? changedPath = null)
    {
        var sourceBytes = Encoding.UTF8.GetBytes("statement receipt source\n");
        var atom = new DigestionAtom(
            "manual/statement-receipt",
            0,
            sourceBytes.Length,
            ImmutableArray.CreateRange(sourceBytes),
            DigestionFingerprint.Compute(sourceBytes),
            []);
        var receipt = new DigestionCoverageReceipt(
            gid,
            atom.Fingerprints.RawSha256,
            receiptStatementId);
        var entry = Entry(
            atom,
            "statement-receipt",
            AtomizerRegistry.NoAtomizerId,
            DigestionMigrationState.Absorbed,
            DigestionTruthState.Closed,
            [gid],
            new DigestionReceipts([receipt], [], [], [], null),
            includeBoundary: true);
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
            [new LeanDeclaration("target", "theorem", "True", [])]);

        return DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.ChangedSet,
            document,
            snapshot,
            AcceptedLean((ModulePath, report)),
            baselineDocument: document,
            changes: RawChangeSet.Create([changedPath ?? ModulePath]));
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
