using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMPhysicalProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite rank-24 products in the original physical coordinates",
        H("Physical Four-Point Product"),
        Blocks(Describe.Lean(DescribeId.Create("fourm-physical-chart-product"),
            DeclarationHandle.Create(
                "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMPhysicalProduct.physical_chart_product"),
            H("Physical rank-24 sector identities"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("A common same-puncture correction carries the finite chart "
                + "product to independent physical oscillator coordinates. The two sector "
                + "relations keep the signed half-current lifts and the Pfaff period factor."))),
            DescribeRole.Theorem))));
}
