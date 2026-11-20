using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SubsetSpectrum;

internal sealed class DigitPeriodCapacityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A bound on the integer levels covered by bounded digits with real weights.",
        H("Integer levels and short digit periods"),
        Blocks(Describe.Lean(
            DescribeId.Create("integer-levels-bounded-by-period-blocks"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/SubsetSpectrum/DigitPeriodCapacity.integral_range_le_period_blocks"),
            H("A missing short period reduces the integer range"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let r, k, n, B and M be natural numbers, with B positive. There are r plus "
                    + "one real weights. A digit can be any integer from zero through k. "
                    + "ShortPeriodsDivide(B,M) means every positive integer below B divides M. "
                    + "NonintegralTotal(M,w) means M times the sum of the weights is nonintegral. "
                    + "Let L be a list of n pairwise distinct integers. IntegerCoverage(r,k,w,L) "
                    + "means every integer in L is represented by a weighted digit vector.")),
                Paragraph(Text(
                    "A positive integer is a period for a coordinate if multiplying its weight "
                    + "by that integer produces integer mass. If each coordinate had a period "
                    + "below B, multiplying every weight by M would give an integer. This would "
                    + "make M times the sum an integer. Some coordinate therefore lacks all short "
                    + "periods. Fix the other digits and divide the selected digit by B, rounding down. "
                    + "Two integral representations with the same other digits and quotient must "
                    + "agree, since a positive difference below B would give a short period. "
                    + "Choosing one representation of each level proves the bound.")),
                Paragraph(Text(
                    "Each arithmetic premise matters even for one weight. With k equal to two, "
                    + "the weight one half covers zero and one. Taking B equal to zero and M equal "
                    + "to one violates the bound without positivity, using Lean's natural-number "
                    + "division convention 2 / 0 = 0, which makes the upper bound one. "
                    + "Taking B equal to three and M "
                    + "equal to one violates it without the divisibility premise. With B equal to "
                    + "three and M equal to two, the integer weight one covers zero, one and two, "
                    + "showing the need for nonintegrality. With the same B and M and weight one "
                    + "third, the upper bound is one. Without distinctness one can list zero "
                    + "twice, and without coverage one can list zero and one even though one "
                    + "has no representation."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula r = F.Id("r");
        Formula k = F.Id("k");
        Formula n = F.Id("n");
        Formula b = F.Id("B");
        Formula m = F.Id("M");
        Formula w = F.Id("w");
        Formula levels = F.Id("L");
        var quotient = new Formula.Floor(new Formula.Fraction(k, b));
        return Disp(Seq(Forall, Sp, r, Sp, k, Sp, n, Sp, b, Sp, m, Sp, w, Sp, levels, Comma, Sp,
            D(0), Sp, Lt, Sp, b, Sp, Land, Sp, Call("ShortPeriodsDivide", b, m),
            Sp, Land, Sp, Call("NonintegralTotal", m, w), Sp, Land, Sp, Call("DistinctLevels", levels, n),
            Sp, Land, Sp, Call("IntegerCoverage", r, k, w, levels),
            Sp, Rightarrow, Sp, n, Sp, Le, Sp, Open, quotient, Plus, D(1), Close,
            Cdot, Sp, Open, k, Plus, D(1), Close, Caret, r));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
