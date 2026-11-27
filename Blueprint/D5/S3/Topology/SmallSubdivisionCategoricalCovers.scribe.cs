using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class SmallSubdivisionCategoricalCoversDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Categorical cover certificates at thirteen and fourteen points",
        H("Categorical cover certificates at thirteen and fourteen points"),
        Blocks(Describe.Lean(
            DescribeId.Create("small-subdivision-cover"),
            DeclarationHandle.Create(
                "D5/S3/Topology/SmallSubdivisionCategoricalCovers.cover_of_census_table"),
            H("The exceptional tables have two categorical pieces after subdivision"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text(
                "For 105 acyclic order tables, monotone-map chains contract the two " +
                "induced vertex sets in the original order. Intersecting chains with those " +
                "sets transfers the partitions to lower covers at the second subdivision."))),
            DescribeRole.Theorem))));
}
