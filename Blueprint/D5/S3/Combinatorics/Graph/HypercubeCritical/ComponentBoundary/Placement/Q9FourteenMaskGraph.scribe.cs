using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9FourteenMaskGraphDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nine vertices with fourteen edges.",
        H("Nine vertices with fourteen edges"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fourteen-edges-on-nine-vertices-impossible"),
                DeclarationHandle.Create(Placement + "Q9FourteenMaskGraph.fourteen_edges_on_nine_vertices_impossible"),
                H("Nine vertices with fourteen edges"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Minimum degree three and fourteen edges force a single degree-four vertex. Its four neighbors and four nonneighbors form the two sides of a bipartite incidence count. The square law rules out the case in which every nonneighbor meets the first side. In the remaining case, the second-common-neighbor condition contradicts the degree budgets."))),
                DescribeRole.Theorem)),
        []));
}
