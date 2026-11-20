using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate;

internal sealed class MaPart08Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Order-four certificate decisions for chunks 139 through 156.",
        H("Order-four certificate decisions for chunks 139 through 156"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ma-part08-boundary08"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part08.boundary08"),
                H("boundary08"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("These are the closed equality states consumed by later parts. Each local chunk has a kernel decision and passes its checked branches to the soundness theorem."))),
                DescribeRole.Theorem))));
}
