using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate;

internal sealed class MaPart11Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Order-four certificate decisions for chunks 194 through 213.",
        H("Order-four certificate decisions for chunks 194 through 213"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ma-part11-boundary11"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part11.boundary11"),
                H("boundary11"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("These are the closed equality states consumed by later parts. Each local chunk has a kernel decision and passes its checked branches to the soundness theorem."))),
                DescribeRole.Theorem))));
}
