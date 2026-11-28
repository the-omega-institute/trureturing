using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Conventions;

internal sealed class WDigitsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "W digits use shifted Fibonacci weights and the canonical Zeckendorf representation.",
        H("W-Digit Convention"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zeckendorf-coordinate-equivalence"),
                DeclarationHandle.Create("D5/S0/Conventions/WDigits.wEncoding"),
                H("Every natural has exactly one canonical W-digit representation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Natural numbers are equivalent to canonical Zeckendorf index lists. "
                    + "IsZeckendorfRep requires every occupied Fibonacci index to be at "
                    + "least two and consecutive occupied indices to differ by at least "
                    + "two; its inverse sums the selected Fibonacci numbers. Thus the "
                    + "equivalence states existence and uniqueness of the binary, "
                    + "nonadjacent W-digit representation, including the empty "
                    + "representation of zero."))),
                DescribeRole.Definition),
            Paragraph(
                Ref("D5/S0/Conventions/WDigits"),
                Text(" fixes the zero-based weights `W(k)=F(k+2)`, hence `1,2,3,5,...`. In the Mathlib build, the Omega weight function reduces to the same Fibonacci iterator. Its initial values and recurrence follow from the standard natural-number weight laws.")),
            Paragraph(
                Text("The canonical algorithm in this interface uses Mathlib's Zeckendorf development. The occupied indices are nonadjacent, decoding returns the original natural number, and no other canonical list decodes to the same value."))),
        anchors: [Anchor.ParseCanonical("mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf")]));
}
