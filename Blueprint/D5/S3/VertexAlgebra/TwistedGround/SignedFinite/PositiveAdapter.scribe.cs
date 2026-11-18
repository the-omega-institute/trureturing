using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.SignedFinite;

internal sealed class PositiveAdapterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed Finite Gaussian PositiveAdapter", H("Signed Finite Gaussian PositiveAdapter"), Blocks(
            Paragraph(Text("The positive-positive signed T table equals the existing finite t for every complex r by finite algebra. The source convolution L, the guarded shift, and the actual period correction are matched exactly; the original positive finite proof is retained.")),
            Describe.Lean(DescribeId.Create("tsigned-positive-eq"), DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/SignedFinite/PositiveAdapter.tSigned_positive_eq"), H("tSigned_positive_eq"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The positive-positive signed T table equals the existing finite t for every complex r by finite algebra. The source convolution L, the guarded shift, and the actual period correction are matched exactly; the original positive finite proof is retained."))), DescribeRole.Theorem))));
}
