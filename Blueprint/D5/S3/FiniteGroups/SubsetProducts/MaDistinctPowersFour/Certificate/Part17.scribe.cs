using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate;

internal sealed class MaPart17Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Order-four certificate decisions for chunks 311 through 318.",
        H("Order-four certificate decisions for chunks 311 through 318"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ma-part17-initial-closed"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part17.initial_closed"),
                H("initial_closed"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The bootstrap partition with sixteen singleton classes is closed. The order-four disjunction uses this closure for arrays without a transversal."))),
                DescribeRole.Theorem))));
}
