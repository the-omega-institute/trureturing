using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Conventions;

internal sealed class WDigitsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/Conventions/WDigits",
            "W digits use shifted Fibonacci weights and the canonical Zeckendorf representation.",
            Anchor.ParseCanonical("mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf")),
        H("W-Digit Convention"),
        Blocks(
            DocumentBlock.Describe.Definition(
                DescribeId.Create("zeckendorf-coordinate-equivalence"),
                H("Every natural has exactly one canonical W-digit representation"),
                LeanDefinition("D5/S0/Conventions/WDigits.wEncoding"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Natural numbers are equivalent to canonical Zeckendorf index lists. "
                    + "IsZeckendorfRep requires every occupied Fibonacci index to be at "
                    + "least two and consecutive occupied indices to differ by at least "
                    + "two; its inverse sums the selected Fibonacci numbers. Thus the "
                    + "equivalence states existence and uniqueness of the binary, "
                    + "nonadjacent W-digit representation, including the empty "
                    + "representation of zero.")))
            ),
            Paragraph(
                Ref("D5/S0/Conventions/WDigits"),
                Text(" fixes the zero-based weights `W(k)=F(k+2)`, hence `1,2,3,5,...`. A digit string is represented by its occupied Fibonacci indices.")),
            Paragraph(
                Text("The module delegates the canonical algorithm and proof to mathlib's Zeckendorf development. It exposes the three repository-facing facts: indices are nonadjacent, decoding returns the original natural number, and no other canonical list decodes to the same value.")))));

    private static LeanDeclarationRef LeanDefinition(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Definition,
            requireNoSorry: true);
}
