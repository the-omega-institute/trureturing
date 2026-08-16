using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.DBonacci;

internal sealed class DBonacciNamesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var d = Id("d");
        var n = Id("n");
        var q = Id("Q");
        var naturals = Id("N");

        return DocumentDefinition.Create(ScribeNode.Create(
            "Boolean words avoiding d consecutive true digits form d-bonacci-sized layers.",
            H("D-Bonacci Names"),
            Blocks(
                Paragraph(Text(
                    "The sequence uses the normalization D_d(0)=0 and D_d(1)=1. Its shifted "
                    + "initial layers satisfy D_d(Q+2)=2^Q for Q<d; after that point each term "
                    + "is the sum of its preceding d terms. A name is scanned with a finite "
                    + "true-run budget, reset by false and decreased by true.")),
                Describe.Lean(
                    DescribeId.Create("d-bonacci-name-layers-have-d-bonacci-cardinality"),
                    DeclarationHandle.Create("D5/S0/Tower/DBonacci/Names.dbonacci_name_card"),
                    H("D-bonacci name layers have d-bonacci cardinality"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("d"),
                        naturals,
                        new Formula.Bind(
                            FormulaQuantifier.ForAll,
                            FormulaIdentifier.Create("Q"),
                            naturals,
                            Equal(
                                Call("card", Call("DBonacciName", d, q)),
                                Call("D", d, Add(q, Num(2))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For Q<d every Boolean word is admissible, giving 2^Q names. For "
                            + "Q>=d, splitting at the first false among the initial d positions "
                            + "gives the d preceding name layers. Strong induction identifies "
                            + "this recurrence with D_d(Q+2), fixing the offset at plus two.")),
                        Paragraph(Text(
                            "The compiled small-case table covers d=2,3,4 and Q=0 through 4. "
                            + "Its rows are 1,2,3,5,8; 1,2,4,7,13; and 1,2,4,8,15.")),
                        Paragraph(Text(
                            "Pinned Mathlib, Loogle, and LeanSearch were queried for k-bonacci, "
                            + "generalized Fibonacci, LinearRecurrence, and binary strings avoiding "
                            + "runs. Mathlib supplies Nat.fib and the generic LinearRecurrence "
                            + "structure, but no exact d-bonacci sequence or avoiding-run count "
                            + "theorem was found, so the finite-state decomposition is proved here."))),
                    DescribeRole.Theorem
                ),
                Describe.Lean(
                    DescribeId.Create("order-three-d-bonacci-is-the-frozen-tribonacci-sequence"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/Names.dbonacci_three_eq_tribonacci"),
                    H("Order-three d-bonacci is the frozen Tribonacci sequence"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("n"),
                        naturals,
                        Equal(Call("D", Num(3), n), Call("T", n)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The order-three recurrence and the first three values agree with the "
                        + "existing Tribonacci module. Strong induction therefore proves pointwise "
                        + "equality without redefining or modifying the frozen specialization."))),
                    DescribeRole.Theorem
                ),
                Describe.Lean(
                    DescribeId.Create("order-two-d-bonacci-is-mathlib-fibonacci"),
                    DeclarationHandle.Create("D5/S0/Tower/DBonacci/Names.dbonacci_two_eq_fib"),
                    H("Order-two d-bonacci is mathlib Fibonacci"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("n"),
                        naturals,
                        Equal(Call("D", Num(2), n), Call("Fib", n)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "At order two the recurrence is D_2(n+2)=D_2(n)+D_2(n+1), with initial "
                        + "values zero and one. The proof applies mathlib's Nat.fib_add_two after "
                        + "establishing the general sequence's two-term equation."))),
                    DescribeRole.Theorem
                )),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Tribonacci/Names")),
            ]));
    }
}
