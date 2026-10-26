using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class SupportedThreeFieldCollisionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three-variable coefficient indices", H("Three-variable coefficient indices"), Blocks(
            Describe.Lean(DescribeId.Create("index3"),
                DeclarationHandle.Create(Prefix + "index3"),
                H("index3"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The native index with the three indicated nonnegative coordinates."))), DescribeRole.Definition))));
}
