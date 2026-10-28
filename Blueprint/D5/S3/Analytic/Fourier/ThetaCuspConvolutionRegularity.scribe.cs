using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Fourier;

internal sealed class ThetaCuspConvolutionRegularityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "C2 regularity and the explicit cusp jump for convolution with the complete translated theta kernel.",
        H("Complete theta cusp convolution regularity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-phi-shifted-cusp-convolution-c2"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Fourier/ThetaCuspConvolutionRegularity."
                    + "actual_phi_shifted_cusp_convolution_C2"),
                H("The complete translated theta convolution is C2"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every a>=0 and every continuous integrable real density b, the literal "
                        + "convolution x↦∫ Phi(a+|x-y|)b(y)dy is C2. Its ordinary second derivative "
                        + "is the convolution with Phi''(a+|x-y|), plus the exact cusp term "
                        + "2*Phi'(a)b(x), including the a=0 evenness case.")),
                    Paragraph(Text(
                        "The proof differentiates the moving cusp away from its single integration "
                        + "point by dominated locally Lipschitz differentiation. It splits the signed "
                        + "first jet into a continuously differentiable part and a right-step jump; "
                        + "the step integrates to the lower cumulative primitive, whose ordinary FTC "
                        + "derivative is b(x). Complete theta jets and their exponential bounds are "
                        + "retained, including the separately paid first mode.")),
                    Paragraph(Text(
                        "This is a repository-derived regularity theorem for the fixed complete theta "
                        + "kernel. It does not assert Gaussian Gamma-domain membership, Suzuki "
                        + "spectral nonvanishing, positivity of arbitrary physical Gram matrices, "
                        + "or the Riemann hypothesis."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Analytic/Fourier/ThetaRadialCurvature")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Zeros/Jensen/OriginalPrimalTailProjection"))
        ]));
}
