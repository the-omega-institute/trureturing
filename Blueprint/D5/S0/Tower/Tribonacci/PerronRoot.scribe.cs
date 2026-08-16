using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.Tribonacci;

internal sealed class TribonacciPerronRootDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var n = Id("n");
        var q = Id("Q");
        var x = Id("x");
        var t = Id("t");
        var naturals = Id("N");
        var reals = Id("R");
        var cubic = Equal(
            Call("pow", x, Num(3)),
            Add(Add(Call("pow", x, Num(2)), x), Num(1)));
        var rootConditions = new Formula.Logic(
            new Formula.Relation(Num(1), FormulaRelationOperator.LessThan, x),
            FormulaLogicOperator.And,
            new Formula.Logic(
                new Formula.Relation(x, FormulaRelationOperator.LessThan, Num(2)),
                FormulaLogicOperator.And,
                cubic));
        var tribonacciRatio = new Formula.Sequence(
            new Formula.Fraction(
                Call("T", Add(n, Num(1))),
                Call("T", n)),
            n,
            naturals);
        var nameRatio = new Formula.Sequence(
            new Formula.Fraction(
                Call("card", Call("TribonacciName", Add(q, Num(1)))),
                Call("card", Call("TribonacciName", q))),
            q,
            naturals);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Tribonacci number and name-count ratios converge to the unique real Perron root.",
            H("Tribonacci Perron Root"),
            Blocks(
                Paragraph(Text(
                    "The existing Tribonacci constant remains the unique source for the base. "
                    + "Factoring its cubic from the count recurrence leaves a stable quadratic "
                    + "error whose positive energy contracts exactly by the inverse base.")),
                Describe.Lean(
                    DescribeId.Create("tribonacci-root-exact-characterization"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/PerronRoot.eq_tribonacciConstant_iff"),
                    H("Exact Tribonacci-root characterization"),
                    StatementSource.FromAuthor(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("x"),
                        reals,
                        new Formula.Logic(
                            Equal(x, t),
                            FormulaLogicOperator.Iff,
                            rootConditions))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Subtracting two cubic equations factors out their root difference. "
                        + "The remaining factor is strictly positive above one, proving "
                        + "uniqueness while the frozen Values module supplies both bounds."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("tribonacci-number-ratio-perron-limit"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/PerronRoot.tribonacci_ratio_tendsto"),
                    H("Tribonacci-number ratio Perron limit"),
                    StatementSource.FromAuthor(Equal(
                        Call("limitAtTop", tribonacciRatio),
                        t)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For e(n)=T(n+1)-tT(n), cubic factorization gives a second-order "
                        + "recurrence. Its positive quadratic energy is multiplied by t^-1 "
                        + "at each step, so e(n) tends to zero and division by positive T(n) "
                        + "yields the ratio limit."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("tribonacci-name-count-ratio-perron-limit"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/PerronRoot.tribonacci_name_card_ratio_tendsto"),
                    H("Tribonacci-name count ratio Perron limit"),
                    StatementSource.FromAuthor(Equal(
                        Call("limitAtTop", nameRatio),
                        t)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The frozen cardinality theorem rewrites each length-Q name count as "
                        + "T(Q+2). Shifting the already proved number-ratio limit by two then "
                        + "gives the exact name-count statement."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Tribonacci/Values")),
            ]));
    }
}
