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
            DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("five-intermediate-points"),
                DeclarationHandle.Create(
                    "D5/S3/Topology/SmallPosetSubdivisionCategory.two_cover_of_five_intermediate"),
                H("Five intermediate points split into two categorical pieces"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
                Blocks(Paragraph(Text(
                    "The five points give at least ten incidences with the upper extrema. One of at most four upper extrema lies above three of the points. " +
                    "The remaining pair shares a lower extremum among the at most three choices. The two common bounds give the categorical partition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("seven-nonmaximal-points"),
                DeclarationHandle.Create(
                    "D5/S3/Topology/SmallPosetSubdivisionCategory.two_cover_of_at_most_seven_nonmaximal"),
                H("Seven points outside the maxima suffice up to fourteen total points"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
                Blocks(Paragraph(Text(
                    "For a connected core with at least two maxima, the two-minimum case is categorical after two subdivisions. " +
                    "Otherwise at most seven nonmaximal points leave at most four intermediate points. " +
                    "If there are four, there are exactly three minima and at most seven maxima, so the common-bound partition applies."))),
                DescribeRole.Theorem))));
}
