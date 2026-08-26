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
    public void DigestionStatusEvaluatorKeepsCoverageReceiptValidWhenSiblingProofBodyChanges()
    {
        var statementId = FrozenStatementReceiptTestData.Id('1');
        var evaluation = Evaluate(
            DeclarationGid,
            statementId,
            statementId,
            FrozenStatementReceiptTestData.Id('2'),
            TargetSource("by exact True.intro"));

        Assert.DoesNotContain(
            evaluation.Entries.Single().Gaps,
            static gap => gap.Code == "coverage-receipt-mismatch");
    }

    [Fact]
    public void DigestionStatusEvaluatorReportsCoverageReceiptMismatchWhenCoveredStatementIdChanges()
    {
        var targetBytes = Encoding.UTF8.GetBytes(TargetSource("by trivial"));
        var previousStatementId = DigestionFingerprint.Compute(targetBytes).RawSha256;
        var evaluation = Evaluate(
            DeclarationGid,
            previousStatementId,
            FrozenStatementReceiptTestData.Id('3'),
            FrozenStatementReceiptTestData.Id('2'),
            Encoding.UTF8.GetString(targetBytes));

        Assert.Contains(
            evaluation.Entries.Single().Gaps,
            static gap => gap.Code == "coverage-receipt-mismatch");
    }

    [Fact]
    public void DigestionStatusEvaluatorUsesModuleStatementIdForModuleGid()
    {
        var moduleStatementId = FrozenStatementReceiptTestData.Id('4');
        var evaluation = Evaluate(
            ModuleGid,
            moduleStatementId,
            FrozenStatementReceiptTestData.Id('1'),
            moduleStatementId,
            TargetSource("by trivial"));

        Assert.DoesNotContain(
            evaluation.Entries.Single().Gaps,
            static gap => gap.Code == "coverage-receipt-mismatch");
    }

    internal static DigestionLedgerEvaluation Evaluate(
        string gid,
        string receiptStatementId,
        string targetStatementId,
        string moduleStatementId,
        string targetSource)
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
                [
                    new FrozenStatementReceiptTestData.Declaration("sibling", FrozenStatementReceiptTestData.Id('2')),
                    new FrozenStatementReceiptTestData.Declaration("target", targetStatementId),
                ]));
        var snapshot = Snapshot(files.Select(static item =>
            (item.Key, Encoding.UTF8.GetBytes(item.Value))).ToArray());
        var report = new LeanFileReport(
            [],
            [
                new LeanDeclaration("sibling", "theorem", "True", []),
                new LeanDeclaration("target", "theorem", "True", []),
            ]);

        return DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.ChangedSet,
            document,
            snapshot,
            AcceptedLean((ModulePath, report)),
            baselineDocument: document,
            changes: RawChangeSet.Create([ModulePath]));
    }

    private static string TargetSource(string siblingProof) => $$"""
        /- GID: {{ModuleGid}}
           generality: G
           mirror-B: none(waiver:test)
           mirror-E: none(waiver:test)
           anchors: []
           digest: Statement receipt fixture. -/
        theorem target : True := by trivial
        theorem sibling : True := {{siblingProof}}
        """;
}
