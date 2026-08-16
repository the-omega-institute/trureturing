using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.DBonacci;

internal sealed class DBonacciPerronRootDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var d = Id("d");
        var x = Id("x");
        var naturals = Id("N");
        var reals = Id("R");
        var betaD = Call("beta", d);
        var characteristic = Equal(
            Call("pow", x, d),
            Call("sumPowersBelow", x, d));
        var rootConditions = new Formula.Logic(
            new Formula.Relation(Num(1), FormulaRelationOperator.LessThan, x),
            FormulaLogicOperator.And,
            new Formula.Logic(
                new Formula.Relation(x, FormulaRelationOperator.LessThan, Num(2)),
                FormulaLogicOperator.And,
                characteristic));
        var orderPremise = new Formula.Relation(
            d,
            FormulaRelationOperator.GreaterThanOrEqual,
            Num(2));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The d-bonacci Perron root is unique, strictly increases with the order, and tends to two.",
            H("D-Bonacci Perron Root"),
            Blocks(
                Paragraph(Text(
                    "For order d at least two, divide the characteristic equation by x^d. "
                    + "The resulting finite reciprocal sum is continuous and strictly decreasing "
                    + "on the positive reals, while its values at one and two straddle one. "
                    + "This gives the unique root in the open interval without numerical approximation.")),
                Describe.Lean(
                    DescribeId.Create("d-bonacci-root-exact-characterization"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/PerronRoot.eq_dbonacciPerronRoot_iff"),
                    H("Exact d-bonacci root characterization"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("d"),
                        naturals,
                        new Formula.Logic(
                            orderPremise,
                            FormulaLogicOperator.Implies,
                            new Formula.Bind(
                                FormulaQuantifier.ForAll,
                                FormulaIdentifier.Create("x"),
                                reals,
                                new Formula.Logic(
                                    Equal(x, betaD),
                                    FormulaLogicOperator.Iff,
                                    rootConditions))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Multiplying the reciprocal sum by x^d and reflecting the finite index "
                        + "range recovers x^d=sum(i=0,...,d-1)x^i. Strict decrease proves that "
                        + "every real in (1,2) satisfying this equation equals the chosen root."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("d-bonacci-characteristic-nontrivial-equation"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/PerronRoot.dbonacci_characteristic_iff_nontrivial_equation"),
                    H("Characteristic and nontrivial equations agree"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("d"),
                        naturals,
                        new Formula.Bind(
                            FormulaQuantifier.ForAll,
                            FormulaIdentifier.Create("x"),
                            reals,
                            new Formula.Logic(
                                NotEqual(x, Num(1)),
                                FormulaLogicOperator.Implies,
                                new Formula.Logic(
                                    characteristic,
                                    FormulaLogicOperator.Iff,
                                    Equal(
                                        Call("pow", x, Add(d, Num(1))),
                                        Subtract(
                                            Multiply(Num(2), Call("pow", x, d)),
                                            Num(1)))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The finite geometric-sum identity introduces the factor x-1. Cancelling "
                        + "that factor away from the trivial root gives x^(d+1)=2x^d-1 in both "
                        + "directions."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("d-bonacci-perron-root-strict-order-monotonicity"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/PerronRoot.dbonacciPerronRoot_strictMonoOn"),
                    H("Perron roots strictly increase with order"),
                    StatementSource.FromAuthor(Call(
                        "StrictMonoOn",
                        Id("beta"),
                        Call("Ici", Num(2)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Passing from d to d+1 adds one strictly positive reciprocal-power term. "
                        + "The next strictly decreasing reciprocal sum can therefore return to "
                        + "one only at a strictly larger argument."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("order-two-perron-root-is-golden-ratio"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/PerronRoot.dbonacciPerronRoot_two_eq_goldenRatio"),
                    H("Order-two root is the golden ratio"),
                    StatementSource.FromAuthor(Equal(
                        Call("beta", Num(2)),
                        Id("goldenRatio"))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Mathlib's goldenRatio lies in (1,2) and satisfies phi^2=phi+1. "
                        + "The exact root characterization therefore identifies beta(2) with it, "
                        + "without introducing another golden-ratio definition."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("order-three-perron-root-is-tribonacci-constant"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/PerronRoot.dbonacciPerronRoot_three_eq_tribonacciConstant"),
                    H("Order-three root is the frozen Tribonacci constant"),
                    StatementSource.FromAuthor(Equal(
                        Call("beta", Num(3)),
                        Id("tribonacciConstant"))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The order-three characteristic sum is beta^2+beta+1. The frozen "
                        + "Tribonacci root characterization then identifies beta(3) with the "
                        + "existing tribonacciConstant rather than redefining that constant."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("d-bonacci-perron-roots-tend-to-two"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/PerronRoot.dbonacciPerronRoot_tendsto_two"),
                    H("Perron roots tend to two"),
                    StatementSource.FromAuthor(Equal(
                        Call("limitAtTop", d, betaD),
                        Num(2))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The nontrivial equation gives the exact deficit "
                            + "2-beta(d)=beta(d)^(-d). Monotonicity bounds beta(d) below by the "
                            + "golden ratio for every d at least two, so the deficit is squeezed "
                            + "by a geometric sequence tending to zero.")),
                        Paragraph(Text(
                            "This is a filter-level Tendsto theorem as d goes to infinity, not a "
                            + "finite table or a numerical proximity check."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Tribonacci/PerronRoot")),
            ]));
    }
}
