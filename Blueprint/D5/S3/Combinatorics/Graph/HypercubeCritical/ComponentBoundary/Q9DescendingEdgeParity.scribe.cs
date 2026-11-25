using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9DescendingEdgeParityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DescendingEdgeParity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Parity of descending edges in the nine-cube",
        H("Parity of descending edges in the nine-cube"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("odd-projected-pair-parity"),
                DeclarationHandle.Create(Module + ".even_sum_doubleFibres_true"),
                H("The total of the odd projected double fibres is even"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reduction of the full Huang eigenvector equation modulo two identifies the parity of each neighbor count with membership. Every two-step descent has two possible intermediate vertices. This pairs the mixed terms and forces the total on odd projected fibres to be even."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nine-axis-parity-contradiction"),
                DeclarationHandle.Create(Module + ".not_all_axes_split_thirteen_one"),
                H("Nine axes cannot each have a thirteen-to-one split"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Either orientation of this split contributes an odd summand. Nine such summands violate the congruence, excluding the size-84 branch after the local size reductions. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9OccupiedFibreParity")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/HuangIntegralNormGap"))]));
}
