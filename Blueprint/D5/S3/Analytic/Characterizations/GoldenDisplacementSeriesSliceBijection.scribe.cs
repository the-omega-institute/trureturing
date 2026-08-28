using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Characterizations;

internal sealed class GoldenDisplacementSeriesSliceBijectionDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Analytic/Characterizations/GoldenDisplacementSeriesSliceBijection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every fixed-second-parameter golden displacement slice is classified by an exact "
        + "summability ray and a bijection onto the open ray above one.",
        H("Fixed-Parameter Golden Displacement Slice Bijection"),
        Blocks(
            Paragraph(Text(
                "For a fixed real w, both affine convergence constraints can be solved for "
                + "s. Their intersection is the open ray strictly above the larger boundary. "
                + "On this exact domain, increasing s strictly lowers the series value.")),
            Describe.Lean(
                DescribeId.Create("golden-displacement-slice-summability-ray"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "golden_displacement_slice_summable_iff"),
                H("The fixed-w summability domain is an open ray"),
                StatementSource.FromAuthor(SummabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For all real s and w, dTerm(s,w) is summable exactly when s is "
                        + "strictly greater than both (1-w)/2 and (1-2w)/3, equivalently "
                        + "strictly greater than their maximum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-displacement-series-slice-bijection"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "golden_displacement_series_slice_bijOn"),
                H("Each fixed-w slice bijects with the open ray above one"),
                StatementSource.FromAuthor(BijectionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real w, restrict the map sending s to the infinite sum of "
                        + "dTerm(s,w) to exactly those s for which the series is summable. "
                        + "This restricted map is a bijection onto the real values strictly "
                        + "greater than one.")),
                    Paragraph(Text(
                        "At the excluded lower boundary, nonnegative partial sums tend to "
                        + "positive infinity. Continuity of a finite partial sum therefore "
                        + "gives a nearby convergent full sum strictly above any target greater "
                        + "than one. Farther along the ray, the full sum tends down to one and "
                        + "is strictly below the target. Continuity attains the target between "
                        + "those points, and strict antitonicity makes that point unique.")),
                    Paragraph(Text(
                        "The codomain excludes the boundary value one, while the "
                        + "summability theorem above shows that the lower parameter "
                        + "boundary is not summable. The bijection gives neither an "
                        + "inverse formula nor quantitative convergence rates."))),
                DescribeRole.Theorem))));

    private static Formula SummabilityFormula()
    {
        Formula s = F.Id("s");
        Formula w = F.Id("w");
        return F.Disp(F.Seq(
            F.Forall, F.Sp, s, F.Comma, F.Sp, w, F.Sp, F.InMacro, F.Sp, Reals(),
            F.Comma, F.RowBreak,
            Call("Summable", Call("dTerm", s, w)),
            F.Sp, F.Leftrightarrow, F.Sp,
            Call("max", Fraction(F.Seq(F.D(1), F.Minus, w), F.D(2)),
                Fraction(F.Seq(F.D(1), F.Minus, F.D(2), w), F.D(3))),
            F.Sp, F.Lt, F.Sp, s, F.Dot));
    }

    private static Formula BijectionFormula()
    {
        Formula s = F.Id("s");
        Formula w = F.Id("w");
        Formula valueMap = F.Seq(
            F.Open, s, F.Sp, F.Mapsto, F.Sp, Tsum(s, w), F.Close);
        Formula domain = F.Seq(
            F.Left, F.OpenBrace, s, F.Sp, F.InMacro, F.Sp, Reals(),
            F.Sp, F.Mid, F.Sp, Call("Summable", Call("dTerm", s, w)),
            F.Right, F.CloseBrace);
        return F.Disp(F.Seq(
            F.Forall, F.Sp, w, F.Sp, F.InMacro, F.Sp, Reals(),
            F.Comma, F.RowBreak,
            Call("BijOn", valueMap, domain, Call("Ioi", F.D(1))), F.Dot));
    }

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        F.Seq(F.Frac, F.Grp(numerator), F.Grp(denominator));

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
