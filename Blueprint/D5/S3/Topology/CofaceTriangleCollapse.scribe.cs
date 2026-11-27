using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class CofaceTriangleCollapseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Graph retraction from comparable cofaces",
        H("Graph retraction from comparable cofaces"),
        Blocks(Describe.Lean(
            DescribeId.Create("coface-graph-retraction"),
            DeclarationHandle.Create(
                "D5/S3/Topology/CofaceTriangleCollapse.exists_contiguous_graph_retraction"),
            H("Comparable cofaces of bounded size give a contiguous graph retraction"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text(
                "Label each vertex by a face with at most three vertices containing it. Suppose the labels of every source face form an inclusion chain. " +
                "Each triangle has a vertex whose label equals the triangle and whose incident faces are all contained in it. " +
                "Replace one such vertex per triangle by a different vertex of the triangle. The replacements define a retraction to a full graph subcomplex. " +
                "The retraction followed by inclusion is contiguous to the identity, takes each vertex into its label, and fixes vertices whose labels have at most two elements."))),
            DescribeRole.Theorem))));
}
