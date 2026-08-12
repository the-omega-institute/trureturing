using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Carrier;

internal sealed class ConjDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden conjugation is an involutive ring equivalence with integral trace.",
        H("Golden Conjugation"),
        Blocks(
            Paragraph(
                Ref("D5/S0/Carrier/Conj"),
                Text(" sends `a + b*phi` to `(a+b) - b*phi`, equivalently replacing `phi` by `1-phi`. The implementation proves that this map preserves addition and multiplication and is its own inverse, then packages those facts as a ring equivalence.")),
            Paragraph(
                Text("The trace is `2a+b`, and the module checks that doubled coordinates commute exactly with mathlib's star operation on `Zsqrtd 5`.")))));
}
