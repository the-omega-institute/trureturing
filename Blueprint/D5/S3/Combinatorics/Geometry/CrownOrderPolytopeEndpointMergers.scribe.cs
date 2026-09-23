using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class CrownOrderPolytopeEndpointMergersDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/lundstrom2025crown");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Selected odd blocks yield connected compatible augmented partitions.",
        H("Merging selected blocks into endpoints"),
        Blocks(
            Paragraph(Text("This is the source-directed construction in Proposition 3.3(i): lower-majority selected blocks join the bottom, upper-majority selected blocks join the top.")),
            Describe.Lean(
                DescribeId.Create("two-sided-merge-ccp-card"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEndpointMergers.twoSidedMergeCCP_card"),
                H("Endpoint merging and quotient cardinality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For n at least two, a connected compatible cycle partition and a selection of its odd blocks determine disjoint lower and upper selections covering the original selection. Merging these selections into the bottom and top endpoints yields an actual quotient with cardinality equal to the original quotient cardinality minus the selected cardinality plus two. Odd-block geometry supplies the required orientation and compatibility."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeOddBlocks"))
        ]));
}
