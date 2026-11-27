using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class SmallAcyclicCategoricalCoversDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Categorical covers for the small acyclic census",
        H("Categorical covers for the small acyclic census"),
        Blocks(Describe.Lean(
            DescribeId.Create("census-categorical-covers"),
            DeclarationHandle.Create(
                "D5/S3/Topology/SmallAcyclicCategoricalCovers.categorical_cover_of_census_table"),
            H("Each listed finite order has an ordinary categorical two-cover"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text(
                "Each of the 105 order tables carries two lower sets and explicit contractions by comparable monotone maps. " +
                "Lean checks the order, the cover and every comparison by kernel reduction. " +
                "The list comes from the published Hasse census and the one-point-extension argument."))),
            DescribeRole.Theorem))));
}
