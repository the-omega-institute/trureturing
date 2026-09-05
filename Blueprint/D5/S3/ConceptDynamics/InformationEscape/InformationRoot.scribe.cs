using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class InformationRootDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One elaboration registers and seals ten frozen theorems and one system theorem.",
        H("Information Theory Root"),
        Blocks(
            Paragraph(Text(
                "Every registered theorem occupies its own arena, so its singleton catalog's unique capture is its whole escape set.")),
            Paragraph(Text(
                "The seal-generated unit and catalog definitions are not described individually: they are emitted in this module under external theorem and arena namespaces, and their repeated final declaration segments are ambiguous to the Scribe declaration-handle resolver.")))));
}
