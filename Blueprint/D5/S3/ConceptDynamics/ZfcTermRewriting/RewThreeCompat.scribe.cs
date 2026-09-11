using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ZfcTermRewriting;

internal sealed class RewThreeCompatDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compatibility wrappers expose canonical ASCII selectors for punctuation-bearing RewThree declarations.",
        H("RewThreeCompat"),
        Blocks(
            Paragraph(Text(
                "This compatibility layer preserves the frozen RewThree source while exposing ASCII GID "
                    + "selectors for source names containing question marks or a subscript. The wrappers "
                    + "carry no axioms and are used only as addressable mirrors."))),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/ConceptDynamics/ZfcTermRewriting/RewThree"))]));
}
