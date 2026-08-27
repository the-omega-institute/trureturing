using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Extrema;

internal sealed class GoldenDisplacementSeriesInfimumDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Analytic/Extrema/GoldenDisplacementSeriesInfimum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Each fixed-w golden series has one as its unattained greatest lower bound.",
        H("Unattained Infima of the Golden Displacement Series"),
        Blocks(
            Paragraph(Text(
                "Fixing the second real parameter still leaves enough convergent values to "
                + "approach one, while every convergent value remains strictly greater than "
                + "one. The corresponding conclusions for the full two-parameter family follow "
                + "as corollaries.")),
            Describe.Lean(
                DescribeId.Create("golden-displacement-series-slice-infimum"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "golden_displacement_series_slice_isGLB"),
                H("Every fixed-parameter slice has greatest lower bound one"),
                StatementSource.FromAuthor(SliceInfimumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each real w, consider exactly the values attained as s varies over "
                        + "parameters for which dTerm(s,w) is summable. One is the greatest lower "
                        + "bound of this slice.")),
                    Paragraph(Text(
                        "The strict series bound supplies the lower-bound half. For greatestness, "
                        + "take s eventually above max(0,2-w). This ensures both hypotheses of "
                        + "dTerm_summable, and the fixed-w limit theorem makes the resulting "
                        + "series values tend to one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-displacement-series-slice-nonattainment"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "one_not_mem_golden_displacement_series_slice"),
                H("No fixed-parameter slice attains one"),
                StatementSource.FromAuthor(SliceNonattainmentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real w, one is absent from the corresponding value set. This "
                        + "is the direct strict consequence of every summable golden displacement "
                        + "series having value greater than one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-displacement-series-full-infimum"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "golden_displacement_series_isGLB"),
                H("The full value set has greatest lower bound one"),
                StatementSource.FromAuthor(FullInfimumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Allowing both real parameters to vary preserves the strict lower bound. "
                        + "Greatestness follows already from the w=0 slice."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-displacement-series-full-nonattainment"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "one_not_mem_golden_displacement_series_values"),
                H("The full value set does not attain one"),
                StatementSource.FromAuthor(FullNonattainmentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "No summable parameter pair has series value one, so the greatest lower "
                        + "bound of the full two-parameter value set is also unattained.")),
                    Paragraph(Text(
                        "These declarations do not identify either value set with the open ray "
                        + "above one, prove that every value greater than one occurs, give a "
                        + "convergence rate, or assert bounds outside the summability region."))),
                DescribeRole.Theorem))));

    private static Formula SliceInfimumFormula()
    {
        Formula w = F.Id("w");
        return F.Disp(F.Seq(
            F.Forall, F.Sp, w, F.Sp, F.InMacro, F.Sp, Reals(), F.Comma, F.RowBreak,
            Call("IsGLB", SliceValueSet(w), F.D(1)), F.Dot));
    }

    private static Formula SliceNonattainmentFormula()
    {
        Formula w = F.Id("w");
        return F.Disp(F.Seq(
            F.Forall, F.Sp, w, F.Sp, F.InMacro, F.Sp, Reals(), F.Comma, F.RowBreak,
            F.Neg, F.Grp(F.D(1), F.Sp, F.InMacro, F.Sp, SliceValueSet(w)), F.Dot));
    }

    private static Formula FullInfimumFormula() =>
        F.Disp(F.Seq(Call("IsGLB", FullValueSet(), F.D(1)), F.Dot));

    private static Formula FullNonattainmentFormula() =>
        F.Disp(F.Seq(
            F.Neg, F.Grp(F.D(1), F.Sp, F.InMacro, F.Sp, FullValueSet()), F.Dot));

    private static Formula SliceValueSet(Formula w)
    {
        Formula x = F.Id("x");
        Formula s = F.Id("s");
        return F.Seq(
            F.Left, F.OpenBrace, x, F.Sp, F.Colon, F.Sp, Reals(),
            F.Sp, F.Mid, F.Sp,
            F.Exists, F.Sp, s, F.Sp, F.InMacro, F.Sp, Reals(), F.Comma, F.Sp,
            Call("Summable", Call("dTerm", s, w)),
            F.Sp, F.Land, F.RowBreak,
            Tsum(s, w), F.Sp, F.Eq, F.Sp, x,
            F.Right, F.CloseBrace);
    }

    private static Formula FullValueSet()
    {
        Formula x = F.Id("x");
        Formula s = F.Id("s");
        Formula w = F.Id("w");
        return F.Seq(
            F.Left, F.OpenBrace, x, F.Sp, F.Colon, F.Sp, Reals(),
            F.Sp, F.Mid, F.Sp,
            F.Exists, F.Sp, s, F.Comma, F.Sp, w,
            F.Sp, F.InMacro, F.Sp, Reals(), F.Comma, F.Sp,
            Call("Summable", Call("dTerm", s, w)),
            F.Sp, F.Land, F.RowBreak,
            Tsum(s, w), F.Sp, F.Eq, F.Sp, x,
            F.Right, F.CloseBrace);
    }

    private static Formula Reals() => F.Seq(F.Mathbb, F.Grp(F.Id("R")));

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
