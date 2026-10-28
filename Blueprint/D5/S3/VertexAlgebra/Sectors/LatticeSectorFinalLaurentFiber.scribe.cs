using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeSectorFinalLaurentFiberDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LatticeSectorFinalLaurentFiber", H("LatticeSectorFinalLaurentFiber"), Blocks(
            Describe.Lean(DescribeId.Create("latticesectorfinallaurentfiber-leftnested"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorFinalLaurentFiber.leftNested"),
                H("leftNested"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual left-nested canonical channel uses the original modes -x-1,-y-1,-z-1 and charge additions ((alpha+beta)+gamma)+delta."))), DescribeRole.Definition))));
}
