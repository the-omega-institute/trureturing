using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower;

internal sealed class GoldenNamesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var q = Id("Q");
        var naturals = Id("N");

        return DocumentDefinition.Create(ScribeNode.Create(
            "Bounded Zeckendorf strings form injectively valued Fibonacci-sized layers.",
            H("Golden Names"),
            Blocks(
                Paragraph(Text(
                    "A length-Q golden name reuses the canonical W-digit representation and "
                    + "requires every occupied Fibonacci index to be below Q plus two. This is "
                    + "equivalent to a length-Q binary word with no adjacent occupied positions.")),
                Describe.Lean(
                    DescribeId.Create("bounded-zeckendorf-golden-name"),
                    DeclarationHandle.Create("D5/S0/Tower/GoldenNames.GoldenName"),
                    H("Bounded Zeckendorf golden name"),
                    StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The representation is a bounded subtype of the repository's existing "
                        + "WDigitString type, so Zeckendorf canonicality remains the single "
                        + "source of the binary nonadjacency constraint."))),
                    DescribeRole.Definition
                ),
                Describe.Lean(
                    DescribeId.Create("golden-name-layers-have-fibonacci-cardinality"),
                    DeclarationHandle.Create("D5/S0/Tower/GoldenNames.golden_name_card"),
                    H("Golden-name layers have Fibonacci cardinality"),
                    StatementSource.FromAuthor(new Formula.Bind(
                                            FormulaQuantifier.ForAll,
                                            FormulaIdentifier.Create("Q"),
                                            naturals,
                                            Equal(
                                                Call("card", Call("GoldenName", q)),
                                                Call("Fib", Add(q, Num(2)))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                                            "Restricting mathlib's Zeckendorf equivalence to values below Fib(Q+2) "
                                            + "gives an equivalence between the name layer and that finite initial "
                                            + "interval. The empty and one-position layers follow without separate "
                                            + "hypotheses."))),
                    DescribeRole.Theorem
                ),
                Describe.Lean(
                    DescribeId.Create("negative-golden-power-name-value"),
                    DeclarationHandle.Create("D5/S0/Tower/GoldenNames.nameValue"),
                    H("Negative golden-power name value"),
                    StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                                            "An occupied Fibonacci index k contributes goldenRatio to the integer "
                                            + "power k minus Q plus two. These exponents are exactly minus one through "
                                            + "minus Q in the position order."))),
                    DescribeRole.Definition
                ),
                Describe.Lean(
                    DescribeId.Create("golden-name-values-are-injective"),
                    DeclarationHandle.Create("D5/S0/Tower/GoldenNames.nameValue_injective"),
                    H("Golden-name values are injective"),
                    StatementSource.FromAuthor(new Formula.Bind(
                                            FormulaQuantifier.ForAll,
                                            FormulaIdentifier.Create("Q"),
                                            naturals,
                                            Call("Injective", Call("nameValue", q)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                                            "A common positive golden power clears the negative exponents. Mathlib's "
                                            + "golden-power Fibonacci identity and golden-ratio irrationality force "
                                            + "the Fibonacci sums to agree, after which Zeckendorf uniqueness identifies "
                                            + "the names."))),
                    DescribeRole.Theorem
                )),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Conventions/WDigits")),
            ]));
    }
}
