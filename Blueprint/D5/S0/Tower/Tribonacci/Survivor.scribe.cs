using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.Tribonacci;

internal sealed class TribonacciSurvivorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var q = Id("Q");
        var x = Id("x");
        var t = Id("t");
        var naturals = Id("N");
        var reals = Id("R");
        var half = new Formula.Fraction(Num(1), Num(2));
        var survivor = Call("tribonacciSurvivor", q, x);
        var hull = Call("tribonacciNameHull", q);

        Formula ForAllQ(Formula body) => new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("Q"),
            naturals,
            body);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Tribonacci-name grid distance has a sharp normalized bound on its hull.",
            H("Tribonacci Survivor Extremality"),
            Blocks(
                Paragraph(Text(
                    "The level-Q grid is the finite image of the frozen increasing name-value "
                        + "enumeration. Its natural hull is tiled by the closed cells between "
                        + "consecutive values.")),
                Describe.Lean(
                    DescribeId.Create("tribonacci-name-grid-is-the-name-value-image"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/Survivor."
                        + "tribonacciNameGrid_eq_nameValue_range"),
                    H("The Tribonacci grid is the intrinsic name-value image"),
                    StatementSource.FromAuthor(ForAllQ(Equal(
                        Call("tribonacciNameGrid", q),
                        Call("range", Call("tribonacciNameValue", q))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The frozen equivalence between the Tribonacci counting interval and "
                            + "admissible names is surjective in both directions, so the indexed "
                            + "and intrinsic descriptions have the same image."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("normalized-tribonacci-survivor-carrier"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/Survivor.tribonacciSurvivor"),
                    H("Normalized Tribonacci survivor carrier"),
                    StatementSource.FromAuthor(ForAllQ(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("x"),
                        reals,
                        Equal(
                            survivor,
                            Multiply(
                                new Formula.Power(t, q),
                                Call(
                                    "infDist",
                                    x,
                                    Call("tribonacciNameGrid", q))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The carrier reuses the frozen Tribonacci constant t and multiplies "
                            + "metric infimum distance to the actual finite grid by t to the "
                            + "level."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("tribonacci-survivor-is-globally-at-most-one-half"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/Survivor.tribonacciSurvivor_le_half"),
                    H("Every Tribonacci hull point has survivor value at most one half"),
                    StatementSource.FromAuthor(ForAllQ(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("x"),
                        reals,
                        new Formula.Logic(
                            new Formula.Relation(
                                q,
                                FormulaRelationOperator.GreaterThanOrEqual,
                                Num(3)),
                            FormulaLogicOperator.Implies,
                            new Formula.Logic(
                                Call("memberOf", x, hull),
                                FormulaLogicOperator.Implies,
                                new Formula.Relation(
                                    survivor,
                                    FormulaRelationOperator.LessThanOrEqual,
                                    half)))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Every point lies in an adjacent cell and is within half that cell's "
                            + "length of an endpoint. The exact three-gap spectrum and its strict "
                            + "ordering identify t^-Q as the largest cell length, so t^Q "
                            + "normalization gives one half."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("first-tribonacci-midpoint-realizes-the-bound"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/Survivor."
                        + "first_tribonacci_midpoint_realizes"),
                    H("The first Tribonacci-gap midpoint realizes one half"),
                    StatementSource.FromAuthor(ForAllQ(new Formula.Logic(
                        new Formula.Relation(
                            q,
                            FormulaRelationOperator.GreaterThanOrEqual,
                            Num(3)),
                        FormulaLogicOperator.Implies,
                        Equal(
                            Call(
                                "tribonacciSurvivor",
                                q,
                                Call("firstTribonacciMidpoint", q)),
                            half)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The fixed first indexed gap has length t^-Q by the frozen prefix "
                            + "recursion. Strict monotonicity places every other grid point "
                            + "outside that gap, making its midpoint exactly half a maximal gap "
                            + "from the grid."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Tribonacci/Gaps")),
            ]));
    }
}
