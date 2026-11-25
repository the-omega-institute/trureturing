using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9SparseOccupiedGramDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SparseOccupiedGram";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sparse occupied Gram obstruction",
        H("Sparse occupied Gram obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sparse-occupied-gram"),
                DeclarationHandle.Create(Module + ".eq_zero_of_sparse_occupied_gram"),
                H("Disjoint column supports force a trivial complementary kernel"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Gram matrices of two row sets sum to a scalar identity. If distinct columns never share a nonzero row in the first matrix, its Gram matrix is diagonal. Each diagonal entry strictly below the common scalar gives a positive diagonal entry in the complementary Gram, forcing its kernel to vanish."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mask-contact"),
                DeclarationHandle.Create(Module + ".maskContact"),
                H("Masked transverse contact"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An occupied projected row meets a paired column by one coordinate flip in the chosen transverse mask."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sparse-mask-kernel"),
                DeclarationHandle.Create(Module + ".eq_zero_of_sparse_mask"),
                H("Sparse contact counts exclude a boundary kernel"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The switching signs turn occupied mask contacts into unit entries. At most one contact per row and fewer contacts per column than the mask size establish strict positivity of the complementary Gram."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-mask-universal-exclusion"),
                DeclarationHandle.Create(Module + ".not_universal_boundary_of_sparse_mask"),
                H("Obstruction to universal weighted sharpness"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Dominant-axis saturation would provide a nonzero empty-fibre kernel for every mask. A sparse contact mask contradicts that requirement. This is the local test for the thirty-two regular order-ninety fold candidates in Hong–Wu–Xia Problem 2."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PositivePairedKernel")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9DominantAxisBoundary"))]));
}
