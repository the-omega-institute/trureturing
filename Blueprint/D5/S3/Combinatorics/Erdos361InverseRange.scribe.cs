using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class Erdos361InverseRangeDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/matijasevick2026forbiddensubsets");

    private static Formula RangeObstruction()
    {
        var theta = F.Theta;
        var epsilon = F.Varepsilon;
        var cutoff = F.Id("K");
        var e = F.Id("E");
        var t = F.Id("T");
        var a = F.Id("A");
        var b = F.Id("B");
        var x = F.Id("x");
        var naturals = F.Seq(F.Mathbb, F.Grp(F.Id("N")));
        var reals = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        var interval = F.Seq(F.OpenBracket, Num(1), F.Comma, e, F.CloseBracket);
        var density = F.Seq(F.Frac, F.Grp(e), F.Grp(Num(4)), F.Plus, epsilon, F.Sp, t,
            F.Leq, F.Vert, F.Sp, a, F.Vert);
        var subsets = F.Seq(F.Forall, F.Sp, b, F.Subseteq, F.Sp, a, F.Comma,
            F.Sum, F.Underscore, F.Grp(F.Seq(x, F.InMacro, F.Sp, b)), x, F.Neq, Num(6), t);
        return F.Disp(F.Seq(F.Forall, theta, F.InMacro, reals, F.Comma,
            theta, F.Lt, Num(3), F.Implies,
            F.Exists, epsilon, F.Gt, Num(0), F.Comma,
            F.Forall, F.Sp, cutoff, F.InMacro, naturals, F.Comma,
            F.Exists, F.Sp, e, F.Comma, t, F.InMacro, naturals, F.Comma,
            F.Exists, F.Sp, a, F.Subseteq, interval, F.Comma,
            F.Open, cutoff, F.Leq, F.Sp, t, F.Land, Num(1), F.Leq, F.Sp, e, F.Land,
            theta, F.Sp, e, F.Leq, Num(6), t, F.Land, F.Sp, density, F.Land, F.Open, subsets, F.Close, F.Close));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For the factor six, every range constant below three fails in the subset-sum inverse theorem.",
        H("A sharp obstruction for least nondivisor four"),
        Blocks(Describe.Lean(
            DescribeId.Create("every-range-below-three-fails"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Erdos361InverseRange.every_range_below_three_fails"),
            H("Every range constant below three fails"),
            StatementSource.FromAuthor(RangeObstruction()),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(
                "Use all multiples of five in the interval and add a terminal segment of the residue class one. "
                + "The target has residue four, so any representation needs at least four terms from the terminal segment. "
                + "The sum of those terms exceeds the target. The two surviving residue classes give a positive density excess."))),
            DescribeRole.Theorem)), []));
}
