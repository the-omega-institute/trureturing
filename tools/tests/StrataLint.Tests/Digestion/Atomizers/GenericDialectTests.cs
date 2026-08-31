using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

/// <summary>
/// A volume whose dialect is declared entirely in data: no C# is written to digest it.
/// These cases are the acceptance condition — a document plus a pattern and some labels.
/// </summary>
public sealed class GenericDialectTests
{
    private const string DialectId = "acceptance-probe";

    private static string RulesWith(string dialectSections) => """
        schema_version = 1

        [[observer.claim_prefixes]]
        prefix = "**Known**"
        locator = "theorem/known"

        [[cone.claim_prefixes]]
        prefix = "定理"
        locator = "theorem/{number}|theorem-form/{number}"

        [[first.genres]]
        token = "定理"
        kind = "theorem"

        [[first.claim_prefixes]]
        prefix = "**Heart**"
        locator = "open/heart"

        [[first.constants]]
        name = "κ"
        locator = "constant/kappa"

        [[second.genres]]
        token = "定理"
        kind = "theorem"

        [[second.markers]]
        role = "trace-note"
        text = "追注"

        [[second.heading_prefixes]]
        prefix = "Supplement "
        locator = "metadata/supplement"

        [[second.heading_prefixes]]
        prefix = "判负册"
        locator = "negative-register/batch"

        [[wm.headings]]
        role = "title"
        text = "Synthetic WM"

        [[wm.headings]]
        role = "appendix"
        text = "Synthetic appendix"

        [[wm.headings]]
        role = "audit"
        text = "Synthetic audit"
        """
        .Replace("[[first.", "[[" + string.Concat("gi", "ct") + ".", StringComparison.Ordinal)
        .Replace("[[second.", "[[" + string.Concat("pz", "g") + ".", StringComparison.Ordinal)
        + "\n\n" + dialectSections;

    private static string ProbeDialect => $$"""
        [[dialect]]
        id = "{{DialectId}}"
        claim = "^\\*\\*(?<kind>\\p{L}+)\\s*(?<number>[0-9]+(?:\\.[0-9]+)+)"

        [[dialect.genre]]
        dialect = "{{DialectId}}"
        token = "定理"
        kind = "theorem"

        [[dialect.genre]]
        dialect = "{{DialectId}}"
        token = "观察"
        kind = "observation"
        """;

    private static TheoryAtomizerRules Load(string data) =>
        TheoryAtomizerDataLoader.Load(
            DigestionTestSupport.Snapshot(
                (TheoryAtomizerDataLoader.DataPath, Encoding.UTF8.GetBytes(data))));

    private static void AssertContentIdentities(IEnumerable<DigestionAtom> atoms, int expectedCount)
    {
        var materialized = atoms.ToArray();
        Assert.Equal(expectedCount, materialized.Length);
        Assert.All(materialized, static atom => Assert.Equal(
            DigestionFingerprint.Compute(atom.RawBytes.AsSpan()).RawSha256,
            atom.Fingerprints.RawSha256));
    }

    private static DigestionLedgerAlignment Align(string atomizerId, byte[] bytes, string data)
    {
        var ledger = DigestionTestSupport.EmptyDocument(atomizerId);
        return DigestionLedgerAligner.Evaluate(
            ledger,
            DigestionTestSupport.Snapshot(
                ("docs/source.md", bytes),
                (TheoryAtomizerDataLoader.DataPath, Encoding.UTF8.GetBytes(data))),
            ledger,
            DigestionAlignmentMode.Ingest);
    }

    [Fact]
    public void ADialectDeclaredInDataDigestsAVolumeWithoutAnyCode()
    {
        var rules = Load(RulesWith(ProbeDialect));
        var bytes = Encoding.UTF8.GetBytes(
            "# 探针卷\n\n**定理 1.1(甲)**。一。\n\n**观察 2.3.4(乙)**。二。\n");

        var document = AtomizerRegistry.Atomize($"dialect:{DialectId}", bytes, rules);

        AssertContentIdentities(document.Claims, 2);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void AnUnregisteredGenreInADeclaredDialectIsAdmittedAsOpen()
    {
        var bytes = Encoding.UTF8.GetBytes("# 探针卷\n\n**未登记体 1.1(甲)**。一。\n");

        var alignment = Align($"dialect:{DialectId}", bytes, RulesWith(ProbeDialect));

        Assert.Empty(alignment.Findings);
        AssertContentIdentities(alignment.Residual.Select(static item => item.Atom), 1);
        Assert.Empty(alignment.Fallbacks);
        Assert.Equal(
            ["未登记体"],
            alignment.GenreRegistryChecks["source"].UnregisteredGenres.ToArray());
    }

    [Fact]
    public void AnUnknownDialectIdIsRefusedAndListsWhatIsDeclared()
    {
        var rules = Load(RulesWith(ProbeDialect));

        var error = Assert.Throws<FormatException>(() =>
            AtomizerRegistry.Atomize("dialect:no-such-volume", Array.Empty<byte>(), rules));

        Assert.Contains("no-such-volume", error.Message, StringComparison.Ordinal);
        Assert.Contains(DialectId, error.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void AGenreBoundToNoDeclaredDialectIsRefusedAtLoad()
    {
        var orphan = ProbeDialect + """

            [[dialect.genre]]
            dialect = "ghost-volume"
            token = "引理"
            kind = "lemma"
            """;

        var error = Assert.Throws<FormatException>(() => Load(RulesWith(orphan)));

        Assert.Contains("ghost-volume", error.Message, StringComparison.Ordinal);
    }

    private const string HeadingDialectId = "heading-probe";

    private static string HeadingProbeDialect => $$"""
        [[dialect]]
        id = "{{HeadingDialectId}}"
        claim = "^(?<kind>\\p{L}+)\\s+(?<number>[0-9]+(?:\\.[0-9]+)+)"
        target = "heading"

        [[dialect.genre]]
        dialect = "{{HeadingDialectId}}"
        token = "定理"
        kind = "theorem"
        """;

    [Fact]
    public void AHeadingTargetDialectDigestsClaimsFromHeadingsOnly()
    {
        var rules = Load(RulesWith(HeadingProbeDialect));
        var bytes = Encoding.UTF8.GetBytes(
            "# 探针卷\n\n## 定理 1.1(甲)\n\n定理 9.9(乙)开头的正文段落。\n\n### 证明\n\n略。\n");

        var document = AtomizerRegistry.Atomize($"dialect:{HeadingDialectId}", bytes, rules);

        AssertContentIdentities(document.Claims, 1);
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void AnUnregisteredGenreOnAHeadingIsAdmittedAsOpen()
    {
        var bytes = Encoding.UTF8.GetBytes("# 探针卷\n\n## 未登记体 1.1(甲)\n");

        var alignment = Align(
            $"dialect:{HeadingDialectId}",
            bytes,
            RulesWith(HeadingProbeDialect));

        Assert.Empty(alignment.Findings);
        AssertContentIdentities(alignment.Residual.Select(static item => item.Atom), 1);
        Assert.Empty(alignment.Fallbacks);
        Assert.Equal(
            ["未登记体"],
            alignment.GenreRegistryChecks["source"].UnregisteredGenres.ToArray());
    }

    [Fact]
    public void AnUnknownDialectTargetIsRefusedAtLoad()
    {
        var invalid = """
            [[dialect]]
            id = "bad-target"
            claim = "^(?<kind>\\p{L}+)\\s+(?<number>[0-9]+)"
            target = "table"
            """;

        var error = Assert.Throws<FormatException>(() => Load(RulesWith(invalid)));

        Assert.Contains("bad-target", error.Message, StringComparison.Ordinal);
        Assert.Contains("table", error.Message, StringComparison.Ordinal);
    }
}
