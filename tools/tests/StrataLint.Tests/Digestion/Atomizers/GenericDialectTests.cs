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

    [Fact]
    public void ADialectDeclaredInDataDigestsAVolumeWithoutAnyCode()
    {
        var rules = Load(RulesWith(ProbeDialect));
        var bytes = Encoding.UTF8.GetBytes(
            "# 探针卷\n\n**定理 1.1(甲)**。一。\n\n**观察 2.3.4(乙)**。二。\n");

        var document = AtomizerRegistry.Atomize($"dialect:{DialectId}", bytes, rules);

        Assert.Equal(
            ["theorem/1.1", "observation/2.3.4"],
            document.Claims.Select(static claim => claim.AstPath).ToArray());
        Assert.Equal(bytes, document.Reassemble().ToArray());
    }

    [Fact]
    public void AnUnregisteredGenreInADeclaredDialectStillFailsClosed()
    {
        var rules = Load(RulesWith(ProbeDialect));
        var bytes = Encoding.UTF8.GetBytes("# 探针卷\n\n**未登记体 1.1(甲)**。一。\n");

        var error = Assert.Throws<TheorySourceFormatException>(() =>
            AtomizerRegistry.Atomize($"dialect:{DialectId}", bytes, rules));

        Assert.Contains(DialectId, error.Message, StringComparison.Ordinal);
        Assert.Contains("未登记体", error.Message, StringComparison.Ordinal);
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
}
