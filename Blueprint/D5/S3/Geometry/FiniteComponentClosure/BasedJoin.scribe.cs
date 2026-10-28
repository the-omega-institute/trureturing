using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.FiniteComponentClosure;

internal sealed class BasedJoinDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A cone collapse is rebased at a native vertex while its quotient map remains unchanged. Exact collapsed-cone traces give relative inverse homotopies and assemble the two-component, common-vertex, and finite-family join decompositions.",
        H("BasedJoin"),
        Blocks(
            Paragraph(Text("A cone collapse is rebased at a native vertex while its quotient map remains unchanged. Exact collapsed-cone traces give relative inverse homotopies and assemble the two-component, common-vertex, and finite-family join decompositions.")))));
}
