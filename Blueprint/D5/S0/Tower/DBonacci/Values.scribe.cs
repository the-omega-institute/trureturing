using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.DBonacci;

internal sealed class DBonacciValuesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var d = Id("d");
        var q = Id("Q");
        var naturals = Id("N");

        return DocumentDefinition.Create(ScribeNode.Create(
            "D-bonacci names acquire real values from the order-d Perron root.",
            H("D-Bonacci Values"),
            Blocks(
                Paragraph(Text(
                    "A true digit in position i contributes beta_d to the negative power i+1. "
                    + "The prefix enumeration follows the same finite run-budget split that "
                    + "counts admissible names, so its order is canonical rather than chosen.")),
                Describe.Lean(
                    DescribeId.Create("d-bonacci-name-value"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/Values.dbonacciNameValue"),
                    H("D-bonacci name value"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("d"),
                        naturals,
                        new Formula.Bind(
                            FormulaQuantifier.ForAll,
                            FormulaIdentifier.Create("Q"),
                            naturals,
                            Call("dbonacciNameValue", d, q)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The value is the finite base-beta_d sum over the true positions of an "
                        + "admissible Boolean word."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("indexed-d-bonacci-name-value"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/Values.indexedNameValue"),
                    H("Indexed d-bonacci name value"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("d"),
                        naturals,
                        new Formula.Bind(
                            FormulaQuantifier.ForAll,
                            FormulaIdentifier.Create("Q"),
                            naturals,
                            Call("indexedNameValue", d, q)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The recursive equivalence lists false-prefix names before true-prefix "
                        + "names at every run-budget state."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("order-three-values-agree-with-tribonacci"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/Values.dbonacciNameValue_three_eq_tribonacciNameValue"),
                    H("Order-three values agree with Tribonacci"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("Q"),
                        naturals,
                        Equal(
                            Call("dbonacciNameValue", Num(3), q, Id("word")),
                            Call("tribonacciNameValue", q, Id("word"))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The already proved identity beta_3=t makes the two word sums equal "
                        + "term by term; the bridge therefore preserves the underlying word."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/DBonacci/PerronRoot")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/DBonacci/Names")),
            ]));
    }
}
