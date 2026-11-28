using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class GraphThickeningForestCoverDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordinary categorical cover number of graph thickenings",
        H("The ordinary categorical cover number of graph thickenings"),
        Blocks(Describe.Lean(
            DescribeId.Create("graph-thickening-ordinary-category-equals-arboricity"),
            DeclarationHandle.Create("D5/S3/Topology/StableCategory/GraphThickeningForestCover.ordinary_cover_number_eq_arboricity"),
            H("The ordinary categorical cover number equals arboricity"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text("Each original vertex is a minimal singleton face. Each edge gives an added maximal triangle. On a cycle an upward comparison fixes all edge maxima and then all the singleton vertices by pairwise intersection. A downward comparison fixes the singletons and then the edge maxima. The cycle stays fixed throughout any order fence from the inclusion. Consequently a categorical lower set can contain only a forest among its edge labels. Conversely, within a forest piece replace each leaf by its unique edge midpoint, then replace that midpoint by the apex. Isolated vertices move directly to the apex. These comparison fences contract the forest pieces, giving exactly the forest covering number when the graph has an edge."))),
            DescribeRole.Theorem))));
}
