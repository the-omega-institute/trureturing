using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class UngradedLocalWordSeriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/FormalSeries/UngradedLocalWordSeries.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed coefficient readout", H("Signed coefficient readout"), Blocks(
            Describe.Lean(DescribeId.Create("signed-index"),
                DeclarationHandle.Create(Prefix + "signedIndex"),
                H("signedIndex"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Convert each nonnegative signed exponent to a native finitely supported multi-index. This index imposes no finite support on a series."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("signed-extend"),
                DeclarationHandle.Create(Prefix + "signedExtend"),
                H("signedExtend"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Extend the native coefficient function by zero whenever any signed exponent is negative."))), DescribeRole.Definition))));
}
