using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour;

internal sealed class MaOrderFourDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A transversal, equal columns or a prescribed motif at order four.",
        H("A transversal, equal columns or a prescribed motif at order four"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ma-orderfour-orderfour"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFour.orderFour"),
                H("orderFour"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/FiniteGroups/best2017latinarrays")),
                Blocks(Paragraph(Text("Best et al., Section 4, classify the two transversal-free order-four types up to trisotopy. The Lean result records the disjunction used by the product argument. It checks forced equality branches from the partition of the sixteen cells into singletons."))),
                DescribeRole.Theorem))));
}
