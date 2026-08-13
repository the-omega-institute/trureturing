using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class ContractionSpectrumOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For amplitude damping on the Bloch axis the three coherence contraction ratios are pointwise "
        + "ordered SLD below KM below RLD, the key lemma behind the contraction-spectrum ordering.",
        H("The Amplitude-Damping Contraction Ratios Are Pointwise Ordered"),
        Blocks(
            Describe.Lean(
                DescribeId.Create(
                    "the-sld-km-and-rld-contraction-ratios-are-pointwise-ordered"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumChannels/ContractionSpectrumOrder.contraction_spectrum_order"),
                H("The SLD, KM, and RLD contraction ratios are pointwise ordered"),
                StatementSource.FromAuthor(Disp(Seq(
                    D(0), Le, Gamma, Sp, Lt, Sp, D(1), Comma, Sp,
                    D(0), Sp, Lt, Sp, F.Id("u"), Sp, Lt, Sp, D(1), Sp,
                    Rightarrow, Sp,
                    F.Id("eta"), Underscore, Grp(F.Id("SLD")), Open, Gamma, Comma, F.Id("u"), Close,
                    Sp, Le, Sp,
                    F.Id("eta"), Underscore, Grp(F.Id("KM")), Open, Gamma, Comma, F.Id("u"), Close,
                    Sp, Le, Sp,
                    F.Id("eta"), Underscore, Grp(F.Id("RLD")), Open, Gamma, Comma, F.Id("u"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a damping parameter gamma in the interval from zero inclusive to one "
                        + "exclusive and an axial Bloch coordinate u in the open unit interval, the "
                        + "three amplitude-damping coherence contraction ratios are pointwise ordered: "
                        + "the SLD ratio is at most the KM ratio, which is at most the RLD ratio. The "
                        + "SLD ratio is the constant one minus gamma; the KM and RLD ratios multiply "
                        + "one minus gamma by the quotient of the respective radial profile (artanh u "
                        + "over u for KM, one over one minus u squared for RLD) at the damped and "
                        + "original coordinates. The profiles are reused verbatim from the frozen "
                        + "AmplitudeDampingContraction module.")),
                    Paragraph(Text(
                        "The ordering reduces to two monotonicity facts of the artanh radial profile "
                        + "on the open unit interval: artanh u over u is increasing (giving the SLD "
                        + "below KM inequality) and one minus u squared times artanh u over u is "
                        + "decreasing (giving the KM below RLD inequality). Each monotonicity is proved "
                        + "from a locally supplied derivative of artanh — genuine new content, since "
                        + "Mathlib has none — together with the enclosing inequalities u over one plus u "
                        + "squared at most artanh u at most u over one minus u squared, which are reused "
                        + "from the frozen DoubleArtanhBounds module rather than re-proved here.")),
                    Paragraph(Text(
                        "This records the pointwise contraction-ratio ordering, the key lemma from "
                        + "which the spectrum ordering of the operational contraction coefficients "
                        + "(their suprema over all input states) follows by monotonicity of the "
                        + "supremum; the sup-level statement is not separately formalized, matching the "
                        + "pointwise coherence-ratio framework of AmplitudeDampingContraction."))),
                DescribeRole.Theorem))));
}
