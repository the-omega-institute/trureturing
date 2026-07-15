using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Conventions;

internal sealed class WDigitsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/Conventions/WDigits",
            "W digits use shifted Fibonacci weights and the canonical Zeckendorf representation."),
        H("W-Digit Convention"),
        Blocks(
            Paragraph(
                Ref("D5/S0/Conventions/WDigits"),
                Text(" fixes the zero-based weights `W(k)=F(k+2)`, hence `1,2,3,5,...`. A digit string is represented by its occupied Fibonacci indices.")),
            Paragraph(
                Text("The module delegates the canonical algorithm and proof to mathlib's Zeckendorf development. It exposes the three repository-facing facts: indices are nonadjacent, decoding returns the original natural number, and no other canonical list decodes to the same value.")))));
}
