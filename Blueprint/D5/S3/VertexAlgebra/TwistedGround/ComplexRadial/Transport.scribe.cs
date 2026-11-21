using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.ComplexRadial;

internal sealed class TransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/ComplexRadial/Transport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real-to-complex transport for the original Gaussian kernels",
        H("The analytic identity on the original source disk"),
        Blocks(
            Paragraph(Text("The literal kernelMode(square,e,f,u,v,z) sums the original coefficients "
                + "over (p,q) ∈ ℕ × ℕ with weights u^p v^q. It uses externalT(e,p,f,q,z) for square = true "
                + "and externalJ(e,p,f,q,z) for square = false.")),
            Describe.Lean(DescribeId.Create("complex-radial-real-supplier"),
                DeclarationHandle.Create(Prefix + "RealRadialSupplier"),
                H("Equality at positive real radii"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For fixed Booleans square, e and f and complex u and v, "
                    + "RealRadialSupplier(square,e,f,u,v) requires that every real 0 < r < 1 with "
                    + "‖u‖ + √r < 1 and ‖v‖ + √r < 1 satisfy "
                    + "kernelMode(square,e,f,u,v,(√r : ℂ)) = signedCandidate(square,e,f,u,v,(r : ℂ))."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("complex-radial-literal-kernel-identity"),
                DeclarationHandle.Create(Prefix + "kernelMode_eq_candidate_complex_of_real"),
                H("Identity on the complex radial disk"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix Booleans square, e and f and complex u, v and z. Given "
                        + "RealRadialSupplier(square,e,f,u,v), ‖u‖ + ‖z‖ < 1 and ‖v‖ + ‖z‖ < 1, "
                        + "kernelMode(square,e,f,u,v,z) = signedCandidate(square,e,f,u,v,z²). "
                        + "The conclusion includes z = 0, the source axes and the source diagonal.")),
                    Paragraph(Text("OriginalGaussianExternalRadialSums.kernel_complex_derivative gives "
                        + "analyticity of the literal sum on the open ball of radius sourceRadius(u,v) "
                        + "via complex differentiability there. candidate_square_analyticOnNhd gives "
                        + "analyticity of the composed candidate on the same ball. For real "
                        + "0 < t < sourceRadius(u,v), taking r = t² gives equality at t. These points "
                        + "accumulate at zero inside the ball. Mathlib's "
                        + "AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure gives equality throughout "
                        + "the preconnected ball."))),
                DescribeRole.Theorem))));
}
