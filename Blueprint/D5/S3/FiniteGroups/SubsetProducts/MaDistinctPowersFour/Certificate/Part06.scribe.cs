using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate;

internal sealed class MaPart06Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Order-four certificate decisions for chunks 100 through 117.",
        H("Order-four certificate decisions for chunks 100 through 117"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ma-part06-boundary06"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part06.boundary06"),
                H("boundary06"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("These are the closed equality states consumed by later parts. Each local chunk has a kernel decision and passes its checked branches to the soundness theorem."))),
                DescribeRole.Theorem))));
}
