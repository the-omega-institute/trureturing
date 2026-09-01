using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class TheoryAtomizerTests
{
    [Theory]
    [InlineData("\n")]
    [InlineData("\r\n")]
    [InlineData("\r")]
    public void WmV1V03OnlyAddsNewVersionAndAuditAtomsWithoutChangingOldAtoms(
        string lineEnding)
    {
        var baseline = AtomizerRegistry.Atomize(
            AtomizerRegistry.WmId,
            Encoding.UTF8.GetBytes(CanonicalWmV02Fixture().ReplaceLineEndings(lineEnding)),
            DigestionTestSupport.Rules);
        var source = Encoding.UTF8.GetBytes(
            CanonicalWmV03Fixture().ReplaceLineEndings(lineEnding));

        var evolved = AtomizerRegistry.Atomize(AtomizerRegistry.WmId, source, DigestionTestSupport.Rules);

        Assert.Equal(2, evolved.Claims
            .Select(static atom => atom.Fingerprints.RawSha256)
            .Except(baseline.Claims.Select(static atom => atom.Fingerprints.RawSha256), StringComparer.Ordinal)
            .Count());
        AssertOldAtomsUnchanged(baseline, evolved);
        Assert.All(evolved.Slices, static slice => Assert.True(slice.IsClaim));
        Assert.Equal(source.Length, evolved.Slices.Sum(static slice => slice.RawBytes.Length));
        Assert.Equal(source, evolved.Reassemble().ToArray());
        AssertSplitIdempotent(AtomizerRegistry.WmId, evolved);
    }

    [Fact]
    public void WmV1V04CanaryProvesTheAppendedAuditGrammarIsNotEnumerated()
    {
        var baseline = AtomizerRegistry.Atomize(
            AtomizerRegistry.WmId,
            Encoding.UTF8.GetBytes(CanonicalWmV03Fixture()),
            DigestionTestSupport.Rules);
        var source = Encoding.UTF8.GetBytes(CanonicalWmV04Fixture());

        var evolved = AtomizerRegistry.Atomize(AtomizerRegistry.WmId, source, DigestionTestSupport.Rules);

        Assert.Equal(2, evolved.Claims
            .Select(static atom => atom.Fingerprints.RawSha256)
            .Except(baseline.Claims.Select(static atom => atom.Fingerprints.RawSha256), StringComparer.Ordinal)
            .Count());
        AssertOldAtomsUnchanged(baseline, evolved);
        Assert.Equal(source, evolved.Reassemble().ToArray());
        AssertSplitIdempotent(AtomizerRegistry.WmId, evolved);
    }

    [Theory]
    [MemberData(nameof(InvalidWmAppendedAuditSources))]
    public void WmV1FailsClosedForInvalidAppendedAuditGrammar(string _, string source)
    {
        var error = Record.Exception(() => AtomizerRegistry.Atomize(
            AtomizerRegistry.WmId,
            Encoding.UTF8.GetBytes(source),
            DigestionTestSupport.Rules));

        Assert.True(error is FormatException or DecoderFallbackException, error?.ToString());
    }

    [Fact]
    public void WmV1IngestionSeesEveryV02ReceiptAndAdmitsExactlyTwoV03Residuals()
    {
        var baseline = AtomizerRegistry.Atomize(
            AtomizerRegistry.WmId,
            Encoding.UTF8.GetBytes(CanonicalWmV02Fixture()),
            DigestionTestSupport.Rules);
        var captures = baseline.Claims
            .Select(static atom => DigestionCasStore.Capture(atom.RawBytes.AsSpan()))
            .ToArray();
        var ledger = DigestionAlignmentTests.WithAtomizer(
            DigestionAlignmentTests.Ledger(
                [],
                baseline.Claims
                    .Select(atom => DigestionAlignmentTests.Entry(
                        atom.Fingerprints.RawSha256["sha256:".Length..],
                        atom))
                    .ToArray()),
            AtomizerRegistry.WmId);
        var sourceBytes = Encoding.UTF8.GetBytes(CanonicalWmV03Fixture());
        var snapshot = DigestionAlignmentTests.Snapshot(sourceBytes, captures);

        var alignment = DigestionLedgerAligner.Evaluate(
            ledger,
            snapshot,
            ledger,
            DigestionAlignmentMode.Ingest);
        var plan = DigestionIngestor.Plan(ledger, snapshot, ledger);

        Assert.Empty(alignment.Findings);
        Assert.All(ledger.RequireDigestionEntries(), entry => Assert.Equal(
            DigestionReceiptAlignment.Seen,
            alignment.AlignmentFor(entry.AtomId)));
        Assert.Equal(2, plan.ResidualOpenAdded);
        var baselineAtomIds = ledger.RequireDigestionEntries()
            .Select(static entry => entry.AtomId)
            .ToHashSet(StringComparer.Ordinal);
        var residual = plan.Document.RequireDigestionEntries()
            .Where(entry => !baselineAtomIds.Contains(entry.AtomId))
            .ToArray();
        Assert.Equal(2, residual.Length);
        Assert.All(residual, static entry => Assert.Matches(
            "^sha256:[0-9a-f]{64}$",
            entry.Fingerprints.RawSha256));
        Assert.All(residual, static entry =>
        {
            Assert.Equal(DigestionMigrationState.Residual, entry.ProjectedStatus.Migration);
            Assert.Equal(DigestionTruthState.Open, entry.ProjectedStatus.Truth);
        });
    }

    public static TheoryData<string, string> InvalidWmAppendedAuditSources
    {
        get
        {
            var v02 = CanonicalWmV02Fixture();
            var v03 = CanonicalWmV03Fixture();
            var v04 = CanonicalWmV04Fixture();
            const string v02Audit =
                "**v0.2 校核**(2026-07-23):追加校核,旧块不改。";
            const string v03Audit =
                "**v0.3 校核**(2026-07-24):勘误 #423/#424,旧块不改。";
            return new TheoryData<string, string>
            {
                {
                    "version skip",
                    v03.Replace("- **v0.3**", "- **v0.4**", StringComparison.Ordinal)
                        .Replace("**v0.3 校核**", "**v0.4 校核**", StringComparison.Ordinal)
                },
                {
                    "version duplicate",
                    v03.Replace(
                        "- **v0.3**(2026-07-24)勘误 #423/#424。",
                        "- **v0.2**(2026-07-24)重复。",
                        StringComparison.Ordinal)
                },
                {
                    "version descending",
                    v03.Replace(
                        "- **v0.2**(2026-07-23)勘误轮结账。\n- **v0.3**(2026-07-24)勘误 #423/#424。",
                        "- **v0.3**(2026-07-24)勘误 #423/#424。\n- **v0.2**(2026-07-23)勘误轮结账。",
                        StringComparison.Ordinal)
                },
                { "version leading zero", v03.Replace("v0.3", "v0.03", StringComparison.Ordinal) },
                { "unknown major version", v03.Replace("v0.3", "v1", StringComparison.Ordinal) },
                {
                    "revision overflow",
                    v03.Replace(
                        "v0.3",
                        "v0.999999999999999999999999999999999999999999999999999999",
                        StringComparison.Ordinal)
                },
                { "ledger-only append", AddWmVersion(v02, 3) },
                { "audit-only append", AddWmAudit(v02, 3) },
                {
                    "ledger audit mismatch",
                    v03.Replace("**v0.3 校核**", "**v0.4 校核**", StringComparison.Ordinal)
                },
                {
                    "nonterminal v0.2 closure missing",
                    v03.Replace(v02Audit, v02Audit.Replace("旧块不改。", "", StringComparison.Ordinal), StringComparison.Ordinal)
                },
                {
                    "closure marker duplicated",
                    v03.Replace(v02Audit, v02Audit + "旧块不改。", StringComparison.Ordinal)
                },
                {
                    "closure marker followed by text",
                    v03.Replace(v02Audit, v02Audit + "夹字", StringComparison.Ordinal)
                },
                {
                    "nonterminal block trailing prose",
                    v03.Replace(
                        v02Audit + "\n\n" + v03Audit,
                        v02Audit + "\n\n可以。\n\n" + v03Audit,
                        StringComparison.Ordinal)
                },
                {
                    "nonterminal block trailing fence",
                    v03.Replace(
                        v02Audit + "\n\n" + v03Audit,
                        v02Audit + "\n\n```text\nresidue\n```\n\n" + v03Audit,
                        StringComparison.Ordinal)
                },
                {
                    "nonterminal block trailing table",
                    v03.Replace(
                        v02Audit + "\n\n" + v03Audit,
                        v02Audit + "\n\n| a |\n| --- |\n| b |\n\n" + v03Audit,
                        StringComparison.Ordinal)
                },
                { "last block trailing prose", v03 + "可以。\n" },
                { "last block trailing fence", v03 + "\n```text\nresidue\n```\n" },
                { "last block trailing table", v03 + "\n| a |\n| - |\n| b |\n" },
                {
                    "current todo missing",
                    v03.Replace(WmCurrentTodoClosure + "\n", string.Empty, StringComparison.Ordinal)
                },
                {
                    "current todo duplicate",
                    v03.Replace(
                        WmCurrentTodoClosure,
                        WmCurrentTodoClosure + "\n\n" + WmCurrentTodoClosure,
                        StringComparison.Ordinal)
                },
                {
                    "current todo moved before v0.1 audit",
                    MoveCurrentTodo(v03, "**v0.1 校核**")
                },
                {
                    "current todo moved after first appended audit",
                    MoveCurrentTodo(v03, "**v0.3 校核**")
                },
                {
                    "current todo literal drift",
                    v03.Replace("**v0.2**(新行追加于版本账", "**v0.3**(新行追加于版本账", StringComparison.Ordinal)
                },
                {
                    "no blank line between appended blocks",
                    v03.Replace("旧块不改。\n\n**v0.3 校核**", "旧块不改。\n**v0.3 校核**", StringComparison.Ordinal)
                },
                {
                    "two blank lines between appended blocks",
                    v03.Replace("旧块不改。\n\n**v0.3 校核**", "旧块不改。\n\n\n**v0.3 校核**", StringComparison.Ordinal)
                },
                {
                    "unknown legacy audit major",
                    v03.Replace("**v0.1 校核**", "**v1 校核**", StringComparison.Ordinal)
                },
                {
                    "legacy audit leading zero",
                    v03.Replace("**v0.1 校核**", "**v0.01 校核**", StringComparison.Ordinal)
                },
                {
                    "v0.3 audit missing while v0.4 remains",
                    v04.Replace("\n\n" + v03Audit, string.Empty, StringComparison.Ordinal)
                },
            };
        }
    }

    private static string CanonicalWmV03Fixture() =>
        AddWmAudit(AddWmVersion(CanonicalWmV02Fixture(), 3), 3);

    private static string CanonicalWmV04Fixture() =>
        AddWmAudit(AddWmVersion(CanonicalWmV03Fixture(), 4), 4);

    private static string AddWmVersion(string source, int revision)
    {
        var prior = revision - 1;
        var priorLine = prior == 2
            ? "- **v0.2**(2026-07-23)勘误轮结账。\n"
            : $"- **v0.{prior}**(2026-07-24)勘误 #423/#424。\n";
        return source.Replace(
            priorLine,
            priorLine + $"- **v0.{revision}**(2026-07-24)勘误 #423/#424。\n",
            StringComparison.Ordinal);
    }

    private static string AddWmAudit(string source, int revision) =>
        source + $"\n**v0.{revision} 校核**(2026-07-24):勘误 #423/#424,旧块不改。\n";

    private static string MoveCurrentTodo(string source, string before)
    {
        var without = source.Replace(
            WmCurrentTodoClosure + "\n\n",
            string.Empty,
            StringComparison.Ordinal);
        return without.Replace(
            before,
            WmCurrentTodoClosure + "\n\n" + before,
            StringComparison.Ordinal);
    }

    private static void AssertOldAtomsUnchanged(
        AtomizedTheoryDocument baseline,
        AtomizedTheoryDocument evolved)
    {
        foreach (var atom in baseline.Claims)
        {
            var unchanged = Assert.Single(
                evolved.Claims,
                candidate => candidate.Fingerprints.RawSha256 == atom.Fingerprints.RawSha256);
            Assert.Equal(atom.RawBytes.ToArray(), unchanged.RawBytes.ToArray());
            Assert.Equal(atom.Fingerprints, unchanged.Fingerprints);
        }
    }
}
