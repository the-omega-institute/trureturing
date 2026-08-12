using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower;

internal sealed class GoldenNamesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var q = Id("Q");
        var naturals = Id("N");

        return DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S0/Tower/GoldenNames",
                "Bounded Zeckendorf strings form injectively valued Fibonacci-sized layers."),
            H("Golden Names"),
            Blocks(
                Paragraph(Text(
                    "A length-Q golden name reuses the canonical W-digit representation and "
                    + "requires every occupied Fibonacci index to be below Q plus two. This is "
                    + "equivalent to a length-Q binary word with no adjacent occupied positions.")),
                DocumentBlock.Describe.Definition(
                    DescribeId.Create("bounded-zeckendorf-golden-name"),
                    H("Bounded Zeckendorf golden name"),
                    LeanDefinition("D5/S0/Tower/GoldenNames.GoldenName"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The representation is a bounded subtype of the repository's existing "
                        + "WDigitString type, so Zeckendorf canonicality remains the single "
                        + "source of the binary nonadjacency constraint.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("golden-name-layers-have-fibonacci-cardinality"),
                    H("Golden-name layers have Fibonacci cardinality"),
                    LeanTheorem("D5/S0/Tower/GoldenNames.golden_name_card"),
                    new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("Q"),
                        naturals,
                        Equal(
                            Call("card", Call("GoldenName", q)),
                            Call("Fib", Add(q, Num(2))))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Restricting mathlib's Zeckendorf equivalence to values below Fib(Q+2) "
                        + "gives an equivalence between the name layer and that finite initial "
                        + "interval. The empty and one-position layers follow without separate "
                        + "hypotheses.")))
                ),
                DocumentBlock.Describe.Definition(
                    DescribeId.Create("negative-golden-power-name-value"),
                    H("Negative golden-power name value"),
                    LeanDefinition("D5/S0/Tower/GoldenNames.nameValue"),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "An occupied Fibonacci index k contributes goldenRatio to the integer "
                        + "power k minus Q plus two. These exponents are exactly minus one through "
                        + "minus Q in the position order.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("golden-name-values-are-injective"),
                    H("Golden-name values are injective"),
                    LeanTheorem("D5/S0/Tower/GoldenNames.nameValue_injective"),
                    new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("Q"),
                        naturals,
                        Call("Injective", Call("nameValue", q))),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "A common positive golden power clears the negative exponents. Mathlib's "
                        + "golden-power Fibonacci identity and golden-ratio irrationality force "
                        + "the Fibonacci sums to agree, after which Zeckendorf uniqueness identifies "
                        + "the names.")))
                )),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Conventions/WDigits")),
            ]));
    }

    private static LeanDeclarationRef LeanDefinition(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Definition,
            requireNoSorry: true);
}
