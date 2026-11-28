using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class DepthZeroElementaryExpansionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Categorical covers across an elementary expansion",
        H("Categorical covers across an elementary expansion"),
        Blocks(Describe.Lean(
            DescribeId.Create("two-lower-sets-after-elementary-expansion"),
            DeclarationHandle.Create("D5/S3/Topology/StableCategory/DepthZeroElementaryExpansion.two_lower_sets_after_elementary_expansion"),
            H("Extension of a two-piece cover"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(
                Paragraph(Text("Suppose the retained complex of an elementary collapse has a categorical cover by two subcomplexes and the expanded complex is connected. After two ordinary barycentric subdivisions, the face poset of the expanded complex has a categorical lower cover of size two.")),
                Paragraph(Text("In the mixed case, collect the vertices omitted by the attaching facets that belong to the second old piece. The resulting face lies in the first piece and in every old attaching face exclusive to that piece. It gives a single contiguity comparison for both new face vertices. For a monochromatic attachment, the opposite piece has a separate new edge that contracts and then moves along an ambient path."))),
            DescribeRole.Theorem))));
}
