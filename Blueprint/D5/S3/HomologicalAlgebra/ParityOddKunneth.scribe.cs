using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class ParityOddKunnethDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/HomologicalAlgebra/ParityOddKunneth";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical cross product in cohomology for two complex-linear parity-odd differentials.",
        H("Künneth equivalence for parity-odd differentials"), Blocks(
            Paragraph(Text("Let V and W be complex vector spaces, each with an endomorphism d satisfying d² = 0 and an involution σ satisfying dσ = −σd. The spaces and their differentials can be different and have arbitrary dimension. For each differential, cohomology is the quotient of its kernel by the image of the map into the kernel induced by d.")),
            Result("parity-odd-tensor-differential", "closedDifferential", "Signed tensor differential",
                DescribeRole.Definition, "On V ⊗ℂ W the differential K acts by K(x ⊗ y) = dV(x) ⊗ y + σV(x) ⊗ dW(y). On a parity eigenvector in V the second term carries the eigenvalue of σV."),
            Result("parity-odd-tensor-square", "closedDifferential_square", "Square-zero law",
                DescribeRole.Theorem, "For every pair of input differentials, K² = 0. On pure tensors the two square terms vanish and the mixed terms cancel by dVσV = −σVdV. The total parity is σV ⊗ σW."),
            Result("parity-odd-kunneth-equiv", "kunnethEquiv", "Cohomology of the signed tensor",
                DescribeRole.Definition, "The cross product gives a complex-linear equivalence H(V,dV) ⊗ℂ H(W,dW) ≃ H(V ⊗ℂ W,K). The maps arise from sections of the image and cycle quotient, averaged against parity. On each factor this gives an odd homotopy h with dh + hd = 1 − ip for the inclusion i and projection p. With E = ip on the first factor, the tensor homotopy hV ⊗ 1 + (EVσV) ⊗ hW supplies the boundary for the composite on K-cycles. The other composite is the identity by pi = 1 in both factors."),
            Result("parity-odd-kunneth-cycle-tensor", "kunnethEquiv_classOf_tmul", "Value on cycle representatives",
                DescribeRole.Theorem, "For arbitrary x in ker dV and y in ker dW, the equivalence sends [x] ⊗ [y] to [x ⊗ y], where x ⊗ y is a genuine K-cycle and the brackets denote the corresponding quotient classes."),
            Result("parity-odd-cross-product-unique", "crossProduct_unique", "Uniqueness of the cross product",
                DescribeRole.Theorem, "Every complex-linear map from H(V,dV) ⊗ℂ H(W,dW) to H(V ⊗ℂ W,K) with the value [x ⊗ y] on every [x] ⊗ [y] equals the cross product. Quotient surjectivity supplies such representatives and pure tensors determine the map."))));

    private static DocumentBlock Result(string id, string declaration, string title, DescribeRole role, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create($"{Module}.{declaration}"),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), role);
}
