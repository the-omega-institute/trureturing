using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.FiniteComponentClosure;

internal sealed class ConeSplitsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The explicit cone-cover quotient and disjoint-join decompositions feed the based finite-component join construction. These are actual maps and homeomorphisms, with no assumed quotient homotopy-extension principle.",
        H("ConeSplits"),
        Blocks(
            Paragraph(Text("The explicit cone-cover quotient and disjoint-join decompositions feed the based finite-component join construction. These are actual maps and homeomorphisms, with no assumed quotient homotopy-extension principle.")))));
}
