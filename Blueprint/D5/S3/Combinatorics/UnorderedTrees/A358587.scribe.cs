using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.UnorderedTrees;

internal sealed class A358587Document : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/wisemanwu2024a358587");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual unordered-tree counts satisfy Wu’s formal generating function and signed recurrence.",
        H("Wu’s Unordered Rooted-Tree Enumeration"),
        Blocks(Describe.Lean(
            DescribeId.Create("oeis-a358587-result"),
            DeclarationHandle.Create("D5/S3/Combinatorics/UnorderedTrees/A358587.result"),
            H("The generating function, initial values and recurrence"),
            StatementSource.FromAuthor(ResultFormula()),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text(
                    "For each natural n, Tₙ is the set of classes of parent maps on Fin n under "
                    + "root-preserving vertex isomorphisms, restricted to trees whose vertex height "
                    + "equals their number of internal vertices. The children are unordered. "
                    + "A singleton has vertex height one and zero internal vertices.")),
                Paragraph(Text(
                    "Pruning the original leaves leaves a unique fork with one short arm. "
                    + "The leaf counts on its spine and tips recover the original isomorphism class. "
                    + "For equal arms the sorted tip counts have the form m+1 and m+d+1, including "
                    + "the diagonal d=0. For unequal arms the two tip counts vary independently. "
                    + "The binomial sums count these decorations for every n.")),
                Paragraph(Text(
                    "Finite coefficient substitution turns the two sums into the generating "
                    + "series over the integers. The displayed denominator has constant coefficient "
                    + "one. The signed recurrence follows by comparing coefficients above degree "
                    + "seven after multiplication by that denominator."))),
            DescribeRole.Theorem,
            new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("oeis-a358587-unordered-rooted-trees"),
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
            new Formula.Power(x, D(2)), Minus, x, Plus, D(1), Close);
        var denominator = Seq(
            new Formula.Power(Seq(Open, x, Minus, D(1), Close), D(2)),
            Open, x, Plus, D(1), Close,
            new Formula.Power(Seq(Open, D(2), x, Minus, D(1), Close), D(2)));
        var recurrence = Seq(D(5), Previous(1), Minus, D(7), Previous(2),
            Minus, Previous(3), Plus, D(8), Previous(4), Minus, D(4), Previous(5));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, n, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Quad, Amp, cardinal),
            Seq(Amp, Land, Sp, Count(D(0)), Eq, D(0)),
            Seq(Amp, Land, Sp, series, Sp, Eq, Sp, new Formula.Fraction(numerator, denominator)),
            Seq(Amp, Land, Sp, Open, Count(D(1)), Comma, Count(D(2)), Comma,
                Count(D(3)), Comma, Count(D(4)), Comma, Count(D(5)), Comma,
                Count(D(6)), Comma, Count(D(7)), Close, Sp, Eq, Sp,
                Open, D(0), Comma, D(0), Comma, D(0), Comma, D(0), Comma,
                D(1), Comma, D(4), Comma, D(1, 4), Close),
            Seq(Amp, Land, Sp, Open, n, Gt, D(7), Sp, Implies, Sp,
                Count(n), Sp, Eq, Sp, recurrence, Close)
        ]));
    }

    private static Formula Count(Formula index) => Seq(F.Id("a"), Open, index, Close);

    private static Formula Previous(byte offset) => Count(Seq(F.Id("n"), Minus, D(offset)));
}
