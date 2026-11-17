using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.BridgeGraph;

internal sealed class NativeThreeRectangularBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeThreeRectangularBound.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete original native width-three scalar-Gram theorem: a < b forces 3c <= 2d.", H("The native three-term rectangular bound"), Blocks(
            Paragraph(Text("For arbitrary a,b,c,d : ℕ, M : Fin 3 → Matrix (Fin a) (Fin b) ℂ, N : Fin 3 → Matrix (Fin d) (Fin c) ℂ, lambda : ℝ, hlambda : 0 < lambda, hab : a < b, and (∑ r, kronecker (M r) (N r))ᴴ * (∑ r, kronecker (M r) (N r)) = (lambda : ℂ) • (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ), the exact conclusion is 3*c ≤ 2*d. No independence or extra dimension premise is added; dependent original factors and all zero dimensions remain included.")),
            Paragraph(Text("Minimal-width reduction and exact whitening preserve the original tensor sum by using an inverse transpose on the right factors. Widths zero and one follow from the injective stack dimension; width two uses the residual compression bound; width three uses the common-vector or neutral-plane geometry, with the vector branch invoking the original Gram common-kernel bound and the plane branch giving 2*c ≤ d.")),
            Describe.Lean(DescribeId.Create("native-three-rectangular-bound"), DeclarationHandle.Create(Prefix + "native_three_rectangular_bound"), H("The complete original theorem"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The theorem retains all four natural dimensions, both arbitrary width-three matrix families, positive lambda, strict a < b, and the exact scalar Gram identity, and concludes 3 * c ≤ 2 * d."))), DescribeRole.Theorem))));
}
