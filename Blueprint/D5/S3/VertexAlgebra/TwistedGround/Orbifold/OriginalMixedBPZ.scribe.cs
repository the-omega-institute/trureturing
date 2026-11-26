using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Orbifold;

internal sealed class OriginalMixedBPZDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalMixedBPZ.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "BPZ Transpose of the Original Mixed Coefficients",
        H("BPZ Transpose of the Original Mixed Coefficients"),
        Blocks(
            Entry("twisted-l-one", "twistedL1", "Lowering by the original stress state",
                "For lattice data D with unit Gram determinant witnessed by hu, L1 is the complex-linear "
                + "endomorphism given by mode two of the original fixed stress state on the negative twisted sector.",
                DescribeRole.Definition),
            Entry("twisted-l-one-value", "twistedL1_val", "Lowering on the underlying tensor",
                "For every negative twisted state u, the underlying tensor of L1 u is the original tensor lowering "
                + "operator T applied to the underlying tensor of u."),
            Entry("original-mixed-bpz-finite", "original_mixed_bpz_finite", "Finite mixed BPZ transpose",
                "Assume the Gram form is positive definite and D has rank 24. Take any integer n and original "
                + "negative twisted states u and v of natural L0 weights H and K, respectively. For every a in "
                + "the full fixed carrier, the source pairing of originalI at mode n on u and v against a equals "
                + "the sum over 0 ≤ j < H − 1 of the actual bilinear form pairing v with the original right "
                + "coefficient at mode 2H − n − j − 2 on L1 to the j-th power applied to u and a. Each term "
                + "is divided by j!, and the sum is multiplied by (−1) to the H-th power. The range uses natural "
                + "subtraction. To compare the coefficients, expand a into its fixed grades and transpose each "
                + "term of the right coefficient. Its second lowering index ell ranges over 0 ≤ ell < K − 1. "
                + "With t = 2H − n − j − 2 and s = n + 1 − ell − 2H + j, the doubled exponent "
                + "−2(t + ell) − 2 is 2s, and the combined phase is (−1) to the (H + s)-th power."),
            Entry("original-mixed-bpz", "original_mixed_bpz", "Algebraic mixed BPZ transpose",
                "Under the same hypotheses, the source pairing equals (−1) to the H-th power times the "
                + "algebraic sum over all natural j of the same divided right-coefficient terms. The terms "
                + "with j ≥ H − 1 vanish by the lower energy bound on the actual twisted tensor."))));

    private static DocumentBlock Entry(string id, string declaration, string heading, string prose,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
