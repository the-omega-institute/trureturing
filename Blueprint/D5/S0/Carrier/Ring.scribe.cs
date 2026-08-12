using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Carrier;

internal sealed class RingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden integers use integral coordinates with the quadratic relation built into multiplication.",
        H("Golden Integer Ring"),
        Blocks(
            Paragraph(
                Ref("D5/S0/Carrier/Ring"),
                Text(" represents each element of `Z[phi]` by its unique integral coordinates `a + b*phi`. Multiplication reduces `phi^2` to `phi + 1`, so the defining quadratic relation is part of computation rather than an added axiom.")),
            Paragraph(
                Text("The map to mathlib's `Zsqrtd 5` stores twice the algebraic integer: `a + b*phi` becomes `(2a+b) + b*sqrt(5)`. Consequently it is additive, injective, and its multiplication law carries an explicit factor of two; it is deliberately not mislabeled as a ring homomorphism.")))));
}
