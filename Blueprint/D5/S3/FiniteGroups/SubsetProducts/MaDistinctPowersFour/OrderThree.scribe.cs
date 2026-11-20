using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour;

internal sealed class MaOrderThreeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A row- and column-injective array of order three has a transversal.",
        H("A row- and column-injective array of order three has a transversal"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ma-orderthree-orderthree"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderThree.orderThree"),
                H("orderThree"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/best2017latinarrays")),
                Blocks(Paragraph(Text("Best et al., Section 4, list no transversal-free arrays of order three. The Lean proof checks the six column permutations and transfers the Boolean equality table to the original labels."))),
                DescribeRole.Theorem))));
}
