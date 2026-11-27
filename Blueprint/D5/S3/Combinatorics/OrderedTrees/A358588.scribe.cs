using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.OrderedTrees;

internal sealed class A358588Document : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/wisemanwu2024a358588");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual ordered-tree counts satisfy Wu’s formal generating function and signed recurrence.",
        H("Wu’s Ordered Rooted-Tree Enumeration"),
        Blocks(Describe.Lean(
            DescribeId.Create("oeis-a358588-result"),
            DeclarationHandle.Create("D5/S3/Combinatorics/OrderedTrees/A358588.result"),
            H("The generating function, initial values and recurrence"),
            StatementSource.FromAuthor(ResultFormula()),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text(
                    "For each natural n, Tₙ comprises the finite ordered rooted trees with n vertices "
                    + "whose longest root-to-leaf path measured in vertices has length equal to the "
                    + "number of nonleaf vertices. The singleton has vertex height one. "
                    + "The sequence a counts this finite set at each index.")),
                Paragraph(Text(
                    "The series equality is in the ring of formal power series over the integers. "
                    + "The Lean quotient uses the sign-normalized numerator and denominator. "
                    + "The normalized denominator has constant coefficient one, so it has a "
                    + "formal inverse over the integers. Every count in the recurrence is cast "
                    + "to an integer before arithmetic.")),
                Paragraph(Text(
                    "At fixed skeleton size u+3, two mandatory leaves and 2u+5 ordered gaps "
                    + "give weight x^(u+5)/(1−x)^(2u+5) per skeleton. Summing over the 2u+1 skeletons "
                    + "at each u uses the weighted geometric series whose coefficient at u is 2u+1. "
                    + "The coefficient proof uses a finite truncation at each degree. "
                    + "Multiplying by the denominator, then comparing coefficients above degree seven, "
                    + "gives the recurrence. The same all-size count formula evaluates a(5), a(6) and a(7)."))),
            DescribeRole.Theorem,
            new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("oeis-a358588-ordered-rooted-trees"),
                ResolutionKind.Proved)))));

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var x = F.Id("x");
        var set = new Formula.Subscript(F.Id("T"), n);
        var cardinal = Seq(Operatorname, Grp(F.Id("Finite")), Open, set, Close, Sp, Land, Sp,
            Count(n), Sp, Eq, Sp, Lvert, Sp, set, Rvert);
        var coefficients = Seq(Sum, Underscore, Grp(F.Id("k"), Eq, D(0)), Caret, Grp(Infty));
        var series = Seq(coefficients, Sp, Count(F.Id("k")),
            new Formula.Power(x, F.Id("k")));
        var numerator = Seq(new Formula.Power(x, D(5)), Open,
            Minus, new Formula.Power(x, D(2)), Plus, x, Minus, D(1), Close);
        var denominator = Seq(
            new Formula.Power(Seq(Open, x, Minus, D(1), Close), D(3)),
            new Formula.Power(Seq(Open, new Formula.Power(x, D(2)), Minus, D(3), x,
                Plus, D(1), Close), D(2)));
        var recurrence = Seq(D(9), Previous(1), Minus, D(3, 2), Previous(2),
            Plus, D(5, 8), Previous(3), Minus, D(5, 8), Previous(4),
            Plus, D(3, 2), Previous(5), Minus, D(9), Previous(6), Plus, Previous(7));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, n, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Quad, Amp, cardinal),
            Seq(Amp, Land, Sp, Count(D(0)), Eq, D(0)),
            Seq(Amp, Land, Sp, series, Sp, Eq, Sp, new Formula.Fraction(numerator, denominator)),
            Seq(Amp, Land, Sp, Open, Count(D(1)), Comma, Count(D(2)), Comma,
                Count(D(3)), Comma, Count(D(4)), Comma, Count(D(5)), Comma,
                Count(D(6)), Comma, Count(D(7)), Close, Sp, Eq, Sp,
                Open, D(0), Comma, D(0), Comma, D(0), Comma, D(0), Comma,
                D(1), Comma, D(8), Comma, D(4, 1), Close),
            Seq(Amp, Land, Sp, Open, n, Gt, D(7), Sp, Implies, Sp,
                Count(n), Sp, Eq, Sp, recurrence, Close)
        ]));
    }

    private static Formula Count(Formula index) => Seq(F.Id("a"), Open, index, Close);

    private static Formula Previous(byte offset) => Count(Seq(F.Id("n"), Minus, D(offset)));
}
