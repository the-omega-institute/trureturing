using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class ActualThreeNodeFiniteAlgebraDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual three-node FiniteAlgebra", H("Actual three-node FiniteAlgebra"),
        Blocks(
            Paragraph(Text("The exact finite coefficients and their trace and determinant identities are stated with the literal three-node arithmetic source Gram in ActualThreeNodeSourceHeadBridge.")))));
}
