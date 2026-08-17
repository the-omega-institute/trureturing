using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.DBonacci;

internal sealed class DBonacciSurvivorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var d = Id("d");
        var q = Id("Q");
        var x = Id("x");
        var beta = Call("beta", d);
        var naturals = Id("N");
        var reals = Id("R");

        Formula ForAllQ(Formula body) => new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("Q"),
            naturals,
            body);

        Formula ForAllX(Formula body) => new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            reals,
            body);

        var survivor = Call("dbonacciSurvivor", d, q, x);
        var carrierFormula = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("d"),
            naturals,
            ForAllQ(ForAllX(Equal(
                survivor,
                Multiply(
                    new Formula.Power(beta, q),
                    Call("infDist", x, Call("dbonacciNameGrid", d, q)))))));
        var specializationFormula = ForAllQ(ForAllX(Equal(
            Call("dbonacciSurvivor", Num(3), q, x),
            Call("tribonacciSurvivor", q, x))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "D-bonacci name grids carry a common normalized distance, compatible with order three.",
            H("D-Bonacci Survivor Carrier"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("intrinsic-d-bonacci-name-grid"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/Survivor.dbonacciNameGrid"),
                    H("Intrinsic d-bonacci name grid"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("d"),
                        naturals,
                        ForAllQ(Equal(
                            Call("dbonacciNameGrid", d, q),
                            Call("range", Call("dbonacciNameValue", d, q)))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The level-Q grid is the image of every admissible d-bonacci name under "
                            + "the existing intrinsic value map."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("normalized-d-bonacci-survivor-carrier"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/Survivor.dbonacciSurvivor"),
                    H("Normalized d-bonacci survivor carrier"),
                    StatementSource.FromAuthor(carrierFormula),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "At each level, metric infimum distance to the actual finite name grid "
                            + "is normalized by the Q-th power of the already frozen Perron root."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("order-three-survivor-specialization"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/Survivor."
                        + "dbonacciSurvivor_three_eq_tribonacciSurvivor"),
                    H("Order-three specialization is the frozen Tribonacci carrier"),
                    StatementSource.FromAuthor(specializationFormula),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The general order-three admissibility predicate has the same names as "
                            + "the frozen Tribonacci automaton, their value images agree, and the "
                            + "existing Perron-root bridge identifies the normalization constants."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("d-bonacci-survivor-nonnegative"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/Survivor.dbonacciSurvivor_nonneg"),
                    H("Every survivor value of order at least two is nonnegative"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("d"),
                        naturals,
                        ForAllQ(ForAllX(new Formula.Logic(
                            new Formula.Relation(
                                d,
                                FormulaRelationOperator.GreaterThanOrEqual,
                                Num(2)),
                            FormulaLogicOperator.Implies,
                            new Formula.Relation(
                                survivor,
                                FormulaRelationOperator.GreaterThanOrEqual,
                                Num(0))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Positivity of the Perron normalization and nonnegativity of metric "
                            + "infimum distance give the sign directly."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/DBonacci/Values")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Tribonacci/Survivor")),
            ]));
    }
}
