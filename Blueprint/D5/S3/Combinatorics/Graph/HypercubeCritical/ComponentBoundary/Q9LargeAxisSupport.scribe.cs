using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9LargeAxisSupportDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LargeAxisSupport";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Many large positive boundary blocks",
        H("Many large positive boundary blocks"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-six-large-axes"),
                DeclarationHandle.Create(Module + ".exists_small_component_with_six_large_axes"),
                H("Six large weighted kernel blocks in one component"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In a hypothetical 258-vertex subcubic set, two disjoint components support universal weighted boundary kernels. The smaller has at most 126 vertices by isotropic edge counts. Each eight-column positive block requires a full star and distinct axes have disjoint 32-vertex footprints. At least six axes therefore carry a fixed occupied-connected block of at least nine columns with a strictly positive switched kernel at positive weights. This is an actual necessary condition for Hong–Wu–Xia Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PositiveSpectrumApplication")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarFootprintPacking"))]));
}
