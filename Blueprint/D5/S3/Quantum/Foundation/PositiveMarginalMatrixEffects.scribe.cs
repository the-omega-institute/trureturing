using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class PositiveMarginalMatrixEffectsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/PositiveMarginalMatrixEffects.";
    private static readonly LibraryNoteRef Note =
        LibraryNoteRef.Create("D5/L/QuantumStates/barnumhilgert2019spectral");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual preparation is the product effect under trace duality and induces an onto real linear isometry of the Hilbert tensor product.",
        H("Product-effect pairing and the actual tensor isometry"),
        Blocks(
            Law("four-vector-pairing", "prep_pairing", "Exact four-vector trace pairing",
                "Under Marginals and Spans, the joint pairing of M(f,g) with M(x,y) equals the product of the local pairings of f with x and g with y. Here M(f,g) is N(f,g) by (16). The identity quantifies over all four Hermitian inputs, as in (17).",
                DescribeRole.Theorem),
            Law("product-effect-interval", "product_effect_interval", "The actual product of proper effects is proper",
                "For f and g in their full local PSD unit intervals, M(f,g) is in the joint PSD unit interval. Its complement is M(I-f,g) + M(I,I-g).",
                DescribeRole.Theorem),
            Law("proper-effect-separation", "proper_effects_separate", "Full local effect intervals separate joint vectors",
                "If the trace readings of two joint vectors agree against the actual adjoint Jordan products for all proper local f and g, the two joint vectors are equal. Local frame projections suffice for the spectral extension, and real product spanning completes the argument.",
                DescribeRole.Theorem),
            Law("tensor-isometry", "tensorIsometry", "The actual preparation defines an onto real linear isometry",
                "The domain is the real Hilbert tensor product of the trace inner product spaces H(a) and H(b). Its codomain is the whole H(d). Equation (17) extends from simple tensors to the entire tensor space, and product spanning gives surjectivity.",
                DescribeRole.Definition),
            Law("actual-tensor-linearization", "tensorIsometry_toLinearMap", "The underlying linear map is precisely the lift of M",
                "The linear map of the isometry is TensorProduct.lift M. In particular tensorIsometry_tmul gives M(x,y) on the simple tensor x tensor y.",
                DescribeRole.Theorem))));

    private static DocumentBlock Law(string id, string selector, string heading, string explanation, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + selector),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Note),
            Blocks(Paragraph(Text(explanation))), role);
}
