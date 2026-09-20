using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class CrownOrderPolytopeTwoExceptionsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/lundstrom2025crown");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two exceptional partitions complete the two-block enumeration.",
        H("The two exceptional vertices"),
        Blocks(
            Paragraph(Text("This is source Proposition 3.3(iii), including the two omitted two-block partitions.")),
            Describe.Lean(
                DescribeId.Create("crown-odd-block-merge-two-card"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeTwoExceptions.crownOddBlockMerge_two_card"),
                H("The complete two-block classification"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For n at least two, odd-block merging together with the two explicitly constructed exceptional partitions is a bijection onto all connected compatible partitions with two quotient blocks. Their cardinality is the selected-block count plus two, which supplies the exceptional geometric vertices."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEndpointRecovery"))
        ]));
}
