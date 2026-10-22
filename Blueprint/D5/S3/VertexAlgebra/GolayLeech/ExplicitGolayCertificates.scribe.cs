using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.GolayLeech;

internal sealed class ExplicitGolayCertificatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full polynomial-code kernel certificate.", H("All 64 blocks of 64 messages"),
        Blocks(Describe.Lean(DescribeId.Create("certified-code"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayCertificates.certified_blocks"),
            H("All 64 blocks of 64 messages"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Each block certificate checks every six-coordinate binary tail against the actual polynomial generator. These are closed kernel computations, not Python tables, native_decide, a numerical oracle or an assumed code property."))), DescribeRole.Theorem))));
}
