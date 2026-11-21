using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour;

internal sealed class MaAssemblyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Assemble subgroup-local permutations into one distinct-power enumeration.",
        H("Assemble subgroup-local permutations into one distinct-power enumeration"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ma-assembly-claim-of-orderfour"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Assembly.claim_of_orderFour"),
                H("claim_of_orderFour"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/ma2026distinctpowers")),
                Blocks(Paragraph(Text("Group elements by the cyclic subgroups they generate, and then by class size. The slot map fills the indices and the local permutations ensure distinct powers within classes. Preservation of generated subgroups separates powers from different classes. The final result supplies the order-four premise."))),
                DescribeRole.Theorem))));
}
