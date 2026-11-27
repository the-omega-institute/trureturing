using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class LebesgueStarAssignmentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weak category two in order-complex dimension four",
        H("Weak category two in order-complex dimension four"),
        Blocks(Describe.Lean(
            DescribeId.Create("four-lower-sets-from-two-categorical-opens"),
            DeclarationHandle.Create("D5/S3/Topology/StableCategory/LebesgueStarAssignment.four_lower_sets_of_two_categorical_opens"),
            H("The stable four-piece bound"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(
                Paragraph(Text("For a finite poset with connected order-complex realization and order-complex dimension at most four, a cover of the realization by two categorical open sets gives a cover by four categorical lower sets in an ordinary iterated subdivision of the poset.")),
                Paragraph(Text("Each subdivision shrinks the vertex mesh by a factor at most four fifths in the original coordinate metric. Once that bound falls below the Lebesgue number, each closed star is subordinate to a categorical open. The resulting subcomplex inclusions carry the two contractions, and the four-piece construction passes to the iterated chain poset."))),
            DescribeRole.Theorem))));
}
