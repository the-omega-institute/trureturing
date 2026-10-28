using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.FiniteComponentClosure;

internal sealed class JoinModelsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native sphere-pair joins and common-vertex distribution assemble bouquet joins and nonempty component joins. Dimension-fiber bijections preserve each sphere occurrence and its multiplicity.",
        H("JoinModels"),
        Blocks(
            Paragraph(Text("Native sphere-pair joins and common-vertex distribution assemble bouquet joins and nonempty component joins. Dimension-fiber bijections preserve each sphere occurrence and its multiplicity.")))));
}
