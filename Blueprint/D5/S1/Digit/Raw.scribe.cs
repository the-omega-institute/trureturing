using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class RawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeDocument.Create(
            Header(
                "D5/S1/Digit/Raw",
                "Raw W digits bridge finite multiplicities to mathlib Zeckendorf lists.",
                "GICT-v3.6-I.2-definition-1.4",
                "mathlib-data-nat-fib-zeckendorf"),
            H("Raw W-Digit Strings"),
            Blocks(
                Paragraph(
                    Ref("D5/S1/Digit/Raw"),
                    Text(" represents raw W-digit strings as finitely supported maps from indices to natural coefficients, so a digit position may temporarily carry coefficients larger than one. Evaluation multiplies each coefficient by the W weight `W_i = Fib (i + 2)` and sums; evaluation is additive.")),
                Paragraph(
                    Text("Canonical strings are the binary, nonadjacent ones. The file bridges canonical strings to the mathlib Zeckendorf representation in both directions, with the index offset `W_i = Fib (i + 2)` stated once at the bridge.")))));
}
