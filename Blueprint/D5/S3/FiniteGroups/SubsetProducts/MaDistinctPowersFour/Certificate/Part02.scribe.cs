using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate;

internal sealed class MaPart02Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Order-four certificate decisions for chunks 21 through 41.",
        H("Order-four certificate decisions for chunks 21 through 41"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ma-part02-boundary02"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part02.boundary02"),
                H("boundary02"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("These are the closed equality states consumed by later parts. Each local chunk has a kernel decision and passes its checked branches to the soundness theorem."))),
                DescribeRole.Theorem))));
}
