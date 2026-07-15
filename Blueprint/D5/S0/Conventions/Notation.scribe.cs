using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Conventions;

internal sealed class NotationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/Conventions/Notation",
            "Golden notation remains opt-in and names the carrier, generator, conjugation, and norm."),
        H("Golden Notation"),
        Blocks(
            Paragraph(
                Ref("D5/S0/Conventions/Notation"),
                Text(" provides opt-in notation under the `Golden` scope. The symbols denote the golden integer type, its distinguished generator, the conjugation ring equivalence, and the multiplicative norm homomorphism.")),
            Paragraph(
                Text("The scope is not opened globally. Importers choose it explicitly, preventing collisions with other uses of `phi`, `sigma`, or `N` in mathlib and future theories.")))));
}
