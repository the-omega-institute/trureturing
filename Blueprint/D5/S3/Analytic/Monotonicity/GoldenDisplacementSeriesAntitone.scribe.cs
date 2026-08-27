using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Monotonicity;

internal sealed class GoldenDisplacementSeriesAntitoneDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden displacement sum decreases when either parameter increases.",
        H("Golden Displacement Series Antitonicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-displacement-series-antitone"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Monotonicity/GoldenDisplacementSeriesAntitone."
                    + "golden_displacement_series_antitone"),
                H("Coordinatewise parameter increases lower the displacement sum"),
                StatementSource.FromAuthor(AntitoneFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take a parameter pair (s1,w1) where dTerm is summable. If s1 is "
                        + "at most s2 and w1 is at most w2, then the sum at (s2,w2) is at "
                        + "most the sum at (s1,w1). Only summability of the smaller pair "
                        + "is assumed.")),
                    Paragraph(Text(
                        "At every positive index, both n and nS(n) are at least one. The "
                        + "ordered-exponent theorem for real powers therefore shows that "
                        + "negating and increasing either parameter lowers its factor. The "
                        + "index-zero terms agree, and multiplication preserves the two "
                        + "factor inequalities because all real-power factors are nonnegative.")),
                    Paragraph(Text(
                        "The exact two-constraint characterization of the convergence region "
                        + "shows that the larger pair is summable: both affine constraints "
                        + "increase under the coordinatewise parameter inequalities. Termwise "
                        + "comparison then passes to the sums via Summable.tsum_le_tsum.")),
                    Paragraph(Text(
                        "The implication form avoids a redundant larger-pair summability "
                        + "hypothesis that an AntitoneOn interface would require. Setting either "
                        + "parameter inequality to equality gives antitonicity in the other "
                        + "parameter on every convergent upper ray.")),
                    Paragraph(Text(
                        "The theorem does not claim strict decrease, an equality "
                        + "characterization, a quantitative rate, a converse, or any finite "
                        + "value or order statement outside the exact convergence region."))),
                DescribeRole.Theorem))));

    private static Formula AntitoneFormula()
    {
        Formula s1 = Indexed("s", 1);
        Formula w1 = Indexed("w", 1);
        Formula s2 = Indexed("s", 2);
        Formula w2 = Indexed("w", 2);
        Formula variables = F.Seq(
            s1, F.Comma, F.Sp, w1, F.Comma, F.Sp,
            s2, F.Comma, F.Sp, w2);
        Formula assumptions = F.Seq(
            Call("Summable", Call("dTerm", s1, w1)),
            F.Sp, F.Land, F.Sp, s1, F.Sp, F.Leq, F.Sp, s2,
            F.Sp, F.Land, F.Sp, w1, F.Sp, F.Leq, F.Sp, w2);

        return F.Disp(F.Seq(
            F.Forall, F.Sp, variables, F.Sp, F.InMacro, F.Sp,
            F.Mathbb, F.Grp(F.Id("R")), F.Comma, F.Quad,
            assumptions, F.Sp, F.Rightarrow, F.RowBreak,
            Tsum(s2, w2), F.Sp, F.Leq, F.Sp, Tsum(s1, w1), F.Dot));
    }

    private static Formula Tsum(Formula s, Formula w)
    {
        Formula n = F.Id("n");
        return F.Seq(
            F.Sum, F.Underscore, F.Grp(n, F.Eq, F.D(0)),
            F.Caret, F.Grp(F.Infty), F.Sp, Call("dTerm", s, w, n));
    }

    private static Formula Indexed(string name, byte index) =>
        F.Seq(F.Id(name), F.Underscore, F.D(index));

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
