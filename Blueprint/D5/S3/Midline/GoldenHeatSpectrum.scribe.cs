using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline;

internal sealed class GoldenHeatSpectrumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The excited golden Euler spectrum has heat abscissa one over phi squared and strict L2 threshold one over twice phi squared.",
        H("The Golden Heat Spectrum and Its L2 Midline"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-spectrum-has-abscissa-one-over-phi-squared"),
                DeclarationHandle.Create("D5/S3/Midline/GoldenHeatSpectrum.golden_heat_abscissa"),
                H("The golden spectrum has abscissa one over phi squared"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("IsHeatAbscissa")), Open,
                    F.Id("goldenSpectrum"), Comma, Sp,
                    Frac, Grp(D(1)), Grp(Varphi, Caret, Grp(D(2))), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The golden Euler spectrum has convergence strictly to the right of its heat abscissa and divergence strictly to the left; no boundary behavior is asserted."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("golden-heat-coefficient-is-l2-right-of-the-midline"),
                DeclarationHandle.Create("D5/S3/Midline/GoldenHeatSpectrum.golden_heat_l2_mem"),
                H("The golden heat coefficient is L2 right of the midline"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("s"), Colon, Sp, Mathbb, Grp(F.Id("C")), Comma, Sp,
                    Frac, Grp(D(1)), Grp(D(2), Times, Varphi, Caret, Grp(D(2))), Sp,
                    Lt, Sp, Re, Open, F.Id("s"), Close, Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("MemLp")), Open,
                    Operatorname, Grp(F.Id("heatCoefficient")), Open,
                    F.Id("goldenSpectrum"), Comma, Sp, F.Id("s"), Close, Comma, Sp,
                    D(2), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Above the strict half-abscissa threshold, the universal heat-trace result gives L2 membership for the golden heat coefficient."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("golden-heat-coefficient-is-not-l2-left-of-the-midline"),
                DeclarationHandle.Create("D5/S3/Midline/GoldenHeatSpectrum.golden_heat_l2_not_mem"),
                H("The golden heat coefficient is not L2 left of the midline"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("s"), Colon, Sp, Mathbb, Grp(F.Id("C")), Comma, Sp,
                    Re, Open, F.Id("s"), Close, Sp, Lt, Sp,
                    Frac, Grp(D(1)), Grp(D(2), Times, Varphi, Caret, Grp(D(2))), Sp,
                    Rightarrow, Sp, Neg,
                    Operatorname, Grp(F.Id("MemLp")), Open,
                    Operatorname, Grp(F.Id("heatCoefficient")), Open,
                    F.Id("goldenSpectrum"), Comma, Sp, F.Id("s"), Close, Comma, Sp,
                    D(2), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Below the strict half-abscissa threshold, the universal heat-trace result excludes L2 membership for the golden heat coefficient."))),
                DescribeRole.Theorem
            ))));
}
