using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.GolayLeech;

internal sealed class ExplicitGolayWeightsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full polynomial-code kernel certificate.", H("Universal weight constraints"),
        Blocks(Describe.Lean(DescribeId.Create("certified-code"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/GolayLeech/ExplicitGolayWeights.finite_weight_constraints"),
            H("Universal weight constraints"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Every twelve-coordinate message is reconstructed from an actual six-bit prefix and six-coordinate tail. The finite certificates therefore prove weight divisible by four and minimum nonzero weight eight for the entire linear code, not a sampled subcode."))), DescribeRole.Theorem))));
}
