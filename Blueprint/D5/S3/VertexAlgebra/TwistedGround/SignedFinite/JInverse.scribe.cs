using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.SignedFinite;

internal sealed class JInverseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed Finite Gaussian JInverse", H("Signed Finite Gaussian JInverse"), Blocks(
            Paragraph(Text("The same-sign J formula is a finite left inverse on the coefficients actually produced by twice (u-v)^2. The mixed formula inverts twice (1-uv)^2. Weighted finite second-difference telescoping retains all natural modes without arbitrary-source divisibility claims.")),
            Describe.Lean(DescribeId.Create("jinverse-stencil"), DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/SignedFinite/JInverse.jInverse_stencil"), H("jInverse_stencil"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The same-sign J formula is a finite left inverse on the coefficients actually produced by twice (u-v)^2. The mixed formula inverts twice (1-uv)^2. Weighted finite second-difference telescoping retains all natural modes without arbitrary-source divisibility claims."))), DescribeRole.Theorem))));
}
