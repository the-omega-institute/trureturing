using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Carrier.Powers;

internal sealed class GoldenCriticalBandScalingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden-square scaling maps the second-order band exactly onto a band containing one half.",
        H("Golden Critical-Band Scaling"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-critical-band-scaling"),
                DeclarationHandle.Create(
                    "D5/S0/Carrier/Powers/GoldenCriticalBandScaling"
                    + ".golden_critical_band_scaling"),
                H("The scaled golden band contains the critical midpoint"),
                StatementSource.FromAuthor(Disp(Seq(
                    Varphi, Caret, Grp(D(2)), Times,
                    Open,
                    Frac, Grp(D(1)), Grp(D(2), Times, Varphi, Caret, Grp(D(3))),
                    Comma, Sp,
                    Frac, Grp(D(1)), Grp(Varphi, Caret, Grp(D(3))),
                    Close, Sp, Eq, Sp,
                    Open,
                    Frac, Grp(D(1)), Grp(D(2), Times, Varphi),
                    Comma, Sp,
                    Frac, Grp(D(1)), Grp(Varphi),
                    Close, Sp, Land, Sp,
                    Frac, Grp(D(1)), Grp(D(2)), Sp, InMacro, Sp,
                    Open,
                    Frac, Grp(D(1)), Grp(D(2), Times, Varphi),
                    Comma, Sp,
                    Frac, Grp(D(1)), Grp(Varphi),
                    Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Mathlib's Set.image_mul_left_Ioo theorem gives the image of an open "
                        + "interval under multiplication by a positive scalar. Applying it to the "
                        + "positive scalar phi squared reduces the image claim to cancellation of "
                        + "nonzero powers of phi.")),
                    Paragraph(Text(
                        "The strict bounds 1 < phi < 2 then place one half inside the resulting "
                        + "open interval.")),
                    Paragraph(Text(
                        "Scope: this formalizes only the first sentence of remark 6.20, namely the "
                        + "golden-square interval map and its coverage of one half. It makes no "
                        + "claim about zeta zeros, Z_qc singularities, structural zeros, analytic "
                        + "control, or later pullback consequences in the source atom."))),
                DescribeRole.Theorem)),
        []));
}
