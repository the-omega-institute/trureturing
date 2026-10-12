using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class VertexOperatorTensorProductDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/VertexOperatorTensorProduct.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual integer-mode convolution on the full algebraic tensor carrier.",
        H("Tensor Fields"),
        Blocks(
            Paragraph(Text("For arbitrary complex modules U and V, the constructor uses "
                + "the pinned Mathlib VertexOperator type and the actual algebraic tensor "
                + "product. On u tensor v, normalized mode n is the sum of A_i u tensor "
                + "B_(n-1-i) v. Its support lies in the integer interval from "
                + "n-1-upper(B,v) to upper(A,u). These cutoffs belong to the actual input "
                + "vectors; the endomorphism-valued summand is not globally finitely "
                + "supported. TensorProduct.lift gives the linear extension. Tensor "
                + "induction proves lower truncation on every finite superposition. "
                + "The fieldBilinear operation is separately additive and homogeneous "
                + "in the two input fields. The identity field has its only normalized "
                + "mode at minus one. Tensoring with it embeds the other factor's "
                + "modes by TensorProduct.map; these embeddings are used in the "
                + "proof of translation covariance.")),
            Paragraph(Text("This is reusable operator-field infrastructure for an even "
                + "matter factor tensor a bc field. It does not assume a tensor VOA, "
                + "a Koszul state-assignment rule, Jacobi, Borcherds identities, BRST "
                + "classification, string dynamics or an AdS/CFT conclusion. The "
                + "construction and its identities are derived from the input Laurent "
                + "fields, not premises asserting the desired output field.")),
            Describe.Lean(
                DescribeId.Create("pointwise-finite-support"),
                DeclarationHandle.Create(Prefix + "diagonal_support"),
                H("Exact pointwise diagonal bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two factor Laurent orders cut out a finite "
                    + "integer interval. Empty intervals give zero modes. There are no "
                    + "finite-dimensional, cutoff or positive-energy assumptions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("all-vector-truncation"),
                DeclarationHandle.Create(Prefix + "mode_bounded"),
                H("Every algebraic tensor has a truncation bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Pure tensors use upper(A,u)+upper(B,v)+1; sums "
                    + "use the maximum of the two previously obtained bounds. The "
                    + "result constructs an actual Laurent-series-valued linear map."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("translation-leibniz"),
                DeclarationHandle.Create(Prefix + "derivative_leibniz"),
                H("Derivative Leibniz rule"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The derivative has normalized coefficient "
                    + "-n A_(n-1). The first-factor derivative is genuinely reindexed "
                    + "by i-1. The two weights -(i+1) and -(n-1-i) add to -n. "
                    + "Weighted finite support is proved before sum linearity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tensor-translation-covariance"),
                DeclarationHandle.Create(Prefix + "translation_covariant"),
                H("Translation acts by the sum of the two factor translations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If each input field satisfies [T,A_n]=-n A_(n-1), "
                    + "the tensor field satisfies the same identity with T equal to "
                    + "T_U tensor id plus id tensor T_V. Each lifted translation is "
                    + "passed through a proved finite sum. The two commutators are "
                    + "then combined using the derivative Leibniz theorem."))),
                DescribeRole.Theorem))));
}
