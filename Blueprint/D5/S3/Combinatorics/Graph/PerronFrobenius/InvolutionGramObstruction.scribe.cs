using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PerronFrobenius;

internal sealed class InvolutionGramObstructionDocument : IScribeDocumentDefinition
{
    private const string Graph = "D5/S3/Combinatorics/Graph/PerronFrobenius/";
    private const string Owner = Graph + "InvolutionGramObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive Gram kernels and the fixed space of an involution",
        H("Polynomial continuation of the fixed kernel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("polynomial-involution-obstruction"),
                DeclarationHandle.Create(Owner + "not_forall_pos_fixed_kernel_of_anticommute"),
                H("A coordinate sign change can obstruct a fixed kernel"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let a real polynomial matrix D commute with an involution P. The matrix (I+P)D+(I−P) acts by 2D on the fixed space and by twice the identity on the anti-fixed space. If D has a nonzero fixed kernel at every positive value of the parameter, the determinant of this modified matrix is identically zero.")),
                    Paragraph(Text("At parameter −1 the modified matrix again gives a nonzero fixed kernel vector. An involution J that conjugates D(−1) to D(1) and anticommutes with P sends that vector to a nonzero anti-fixed kernel vector of D(1). This contradicts the hypothesis that the kernel of D(1) is pointwise fixed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-kernel-from-gram-defect"),
                DeclarationHandle.Create(Owner + "exists_positive_gram_kernel_of_det_eq_zero"),
                H("Singular Gram defects give strictly positive eigenvectors"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A singular defect qI−A equal to KKᵀ has a nonzero kernel vector. For irreducible A, taking coordinatewise absolute values cannot increase its defect quadratic form. Since the defect is positive semidefinite, the absolute-value vector still lies in the kernel. Irreducibility propagates any zero of this nonnegative eigenvector through the graph, so all entries are positive."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(Graph + "IrrationalQuadraticBipartition"))]));
}
