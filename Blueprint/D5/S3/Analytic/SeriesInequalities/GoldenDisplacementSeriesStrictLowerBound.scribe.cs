using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.SeriesInequalities;

internal sealed class GoldenDisplacementSeriesStrictLowerBoundDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A summable golden displacement series is strictly greater than one.",
        H("Strict Lower Bound for the Golden Displacement Series"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-displacement-series-strict-lower-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/SeriesInequalities/"
                    + "GoldenDisplacementSeriesStrictLowerBound."
                    + "one_lt_golden_displacement_series"),
                H("The displacement series is strictly greater than one"),
                StatementSource.FromAuthor(StrictLowerBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real parameter pair (s,w) where dTerm(s,w) is summable, "
                        + "the golden displacement series is strictly greater than one.")),
                    Paragraph(Text(
                        "The term at index one equals one. The public bound le_nS shows that "
                        + "nS(2) is positive, so both real-power factors in dTerm(s,w,2) are "
                        + "positive for arbitrary real parameters. Every displacement term is "
                        + "nonnegative.")),
                    Paragraph(Text(
                        "Mathlib's strict HasSum comparison applies the positive witness at "
                        + "index two together with nonnegativity away from index one. It makes "
                        + "the index-one term strictly smaller than the total sum.")),
                    Paragraph(Text(
                        "The summability hypothesis is necessary. At (s,w)=(0,0), the exact "
                        + "two-constraint criterion fails, so the series is not summable and "
                        + "the infinite sum is zero by convention; the unrestricted strict "
                        + "inequality would read 1<0.")),
                    Paragraph(Text(
                        "The theorem does not claim an infimum characterization, an attained "
                        + "minimum, a quantitative gap, or a lower bound outside the summability "
                        + "region."))),
                DescribeRole.Theorem))));

    private static Formula StrictLowerBoundFormula()
    {
        Formula s = F.Id("s");
        Formula w = F.Id("w");
        Formula variables = F.Seq(s, F.Comma, F.Sp, w);

        return F.Disp(F.Seq(
            F.Forall, F.Sp, variables, F.Sp, F.InMacro, F.Sp,
            F.Mathbb, F.Grp(F.Id("R")), F.Comma, F.Quad,
            Call("Summable", Call("dTerm", s, w)),
            F.Sp, F.Rightarrow, F.RowBreak,
            F.D(1), F.Sp, F.Lt, F.Sp, Tsum(s, w), F.Dot));
    }

    private static Formula Tsum(Formula s, Formula w)
    {
        Formula n = F.Id("n");
        return F.Seq(
            F.Sum, F.Underscore, F.Grp(n, F.Eq, F.D(0)),
            F.Caret, F.Grp(F.Infty), F.Sp, Call("dTerm", s, w, n));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { F.Operatorname, F.Grp(F.Id(name)), F.Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(F.Comma);
                pieces.Add(F.Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(F.Close);
        return F.Seq(pieces.ToArray());
    }
}
