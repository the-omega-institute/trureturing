using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.MoebiusLogarithmic;

internal sealed class ReciprocalBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/MoebiusLogarithmic/ReciprocalBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every real prefix of the reciprocal Moebius sum has absolute value at most one.",
        H("The reciprocal Moebius sum"),
        Blocks(
            Describe.Lean(DescribeId.Create("reciprocal-sum"),
                DeclarationHandle.Create(Prefix + "reciprocalSum"),
                H("The exact finite prefix"), StatementSource.FromAuthor(DefinitionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a real cutoff x, m(x) sums the actual integer "
                    + "Moebius coefficients divided by their positive integer indices. "
                    + "The upper endpoint is the natural floor of x. The sum is empty "
                    + "when x is less than one, including negative x."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("uniform-reciprocal-bound"),
                DeclarationHandle.Create(Prefix + "abs_reciprocalSum_le_one"),
                H("A uniform bound at every real cutoff"), StatementSource.FromAuthor(BoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite divisor convolution gives the identity "
                    + "sum mu(n) floor(x/n)=1 for x at least one. Subtracting the "
                    + "integer parts from x m(x) leaves fractional parts. The absolute "
                    + "Moebius coefficient is at most one. Separating the index one "
                    + "leaves its exact fractional part x-floor(x), while the other "
                    + "floor(x)-1 terms are each at most one. Hence |x m(x)| is at "
                    + "most x, which proves the bound for positive x. Empty prefixes "
                    + "supply all remaining real cutoffs."))), DescribeRole.Theorem))));

    private static Formula DefinitionFormula()
    {
        var x = F.Id("x"); var n = F.Id("n");
        return Disp(Seq(Forall, Sp, x, InMacro, Seq(Mathbb, Grp(F.Id("R"))), Comma,
            Equal(Call("m", x), Seq(new Formula.Subscript(Sum,
                Seq(D(1), Le, Sp, n, Le, Sp, Call("floor", x))),
                new Formula.Fraction(Call("mu", n), n)))));
    }

    private static Formula BoundFormula()
    {
        var x = F.Id("x");
        return Disp(Seq(Forall, Sp, x, InMacro, Seq(Mathbb, Grp(F.Id("R"))), Comma,
            Lvert, Sp, Call("m", x), Rvert, Sp, Le, D(1)));
    }
}
