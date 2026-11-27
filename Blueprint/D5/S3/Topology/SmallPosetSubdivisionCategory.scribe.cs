using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class SmallPosetSubdivisionCategoryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A stable category bound for small finite spaces",
        H("A stable category bound for small finite spaces"),
        Blocks(Describe.Lean(
            DescribeId.Create("eleven-points-four-maxima"),
            DeclarationHandle.Create(
                "D5/S3/Topology/SmallPosetSubdivisionCategory.two_cover_of_at_most_eleven_and_four_maxima"),
            H("Two opens cover the second subdivision of the connected core"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text(
                "A connected poset without beat points has at least two minimal points below each nonminimal point, with the dual property above. " +
                "In a poset of at most eleven points with four or more maxima, this permits a partition into two categorical induced subposets. " +
                "The exceptional four-intermediate-point case uses a pair sharing an upper bound and a complementary pair sharing a lower bound. " +
                "The subdivision transfer turns the partition into two categorical opens. This supplies the connected weak-category-at-least-two part of Conjecture 6.1."))),
            DescribeRole.Theorem))));
}
