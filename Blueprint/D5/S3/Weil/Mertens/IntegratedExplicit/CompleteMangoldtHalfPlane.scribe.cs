using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class CompleteMangoldtHalfPlaneDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Mellin transform of the complete Mangoldt remainder",
        H("Absolute convergence in the open right half-plane"),
        Blocks(Describe.Lean(
            DescribeId.Create("arithmetic-mellin-transform"),
            DeclarationHandle.Create(
                "D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtHalfPlane.u_laplace_half_plane"),
            H("Transform of the inclusive integrated prime sum"),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Write x = exp(y). The measure x⁻¹ dx becomes dy, so the Mellin "
                    + "transform of U on x > 1 is the Laplace transform of U(exp(y)) on y > 0. "
                    + "The hypothesis Re(s) > 1 makes the arithmetic series absolutely convergent.")),
                Paragraph(Text(
                    "Fix σ = Re(s). Each nonnegative Mangoldt ramp is multiplied by exp(−sy). "
                    + "Its norm equals the ramp multiplied by exp(−σy). Its norm integral thus "
                    + "equals the real part of the individual ramp transform at σ. The convergent "
                    + "von Mangoldt Dirichlet series at σ makes these norm integrals summable. "
                    + "Tonelli gives absolute integrability of the sum, and its complex integral "
                    + "can be computed term by term, yielding (−ζ′(s)/ζ(s))/(s(s−1)).")),
                Paragraph(Text(
                    "The logarithmic correction integrates to −1/(s−1)² and the linear "
                    + "correction integrates to (1+γ)/(s−1). In the first moment the boundary "
                    + "term at infinity vanishes because y exp(−(σ−1)y) tends to zero."))),
            DescribeRole.Theorem))));
}
