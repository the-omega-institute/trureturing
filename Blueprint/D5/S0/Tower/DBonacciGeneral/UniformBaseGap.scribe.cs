using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.DBonacciGeneral;

internal sealed class DBonacciGeneralUniformBaseGapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var d = Id("d");
        var x = Id("x");
        var leftArm = Id("L");
        var rightArm = Id("R");
        var naturals = Id("N");
        var reals = Id("R");
        var beta = Call("dbonacciPerronRoot", d);
        var diagonalLevel = d;
        var negativeD = Subtract(Num(0), d);
        var diagonalScale = new Formula.Power(beta, negativeD);

        Formula TypedGap(
            Formula order,
            Formula point,
            Formula left,
            Formula right) =>
            Call(
                "IsDBonacciLetterOrbitGap",
                order,
                order,
                point,
                Call("topGapLetter", order),
                left,
                right);

        Formula StandardLargeArm(Formula order)
        {
            var root = Call("dbonacciPerronRoot", order);
            return new Formula.Fraction(
                root,
                Subtract(new Formula.Power(root, Num(2)), Num(1)));
        }

        Formula StandardLowArm(Formula order)
        {
            var root = Call("dbonacciPerronRoot", order);
            return new Formula.Fraction(
                Subtract(Subtract(new Formula.Power(root, Num(2)), root), Num(1)),
                Subtract(new Formula.Power(root, Num(2)), Num(1)));
        }

        var diagonalCardinality = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("d"),
            naturals,
            Equal(
                Call("dbonacci", d, Add(d, Num(2))),
                Subtract(new Formula.Power(Num(2), d), Num(1))));
        var firstZero = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("d"),
            naturals,
            new Formula.Logic(
                new Formula.Relation(
                    d,
                    FormulaRelationOperator.GreaterThanOrEqual,
                    Num(1)),
                FormulaLogicOperator.Implies,
                Equal(Call("indexedNameValue", d, diagonalLevel, Num(0)), Num(0))));
        var firstOne = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("d"),
            naturals,
            new Formula.Logic(
                new Formula.Relation(
                    d,
                    FormulaRelationOperator.GreaterThanOrEqual,
                    Num(2)),
                FormulaLogicOperator.Implies,
                Equal(Call("indexedNameValue", d, diagonalLevel, Num(1)), diagonalScale)));
        var constructionAssumptions = new Formula.Logic(
            new Formula.Relation(
                d,
                FormulaRelationOperator.GreaterThanOrEqual,
                Num(3)),
            FormulaLogicOperator.And,
            new Formula.Logic(
                Equal(x, Multiply(leftArm, diagonalScale)),
                FormulaLogicOperator.And,
                Equal(Add(leftArm, rightArm), Num(1))));
        var uniformConstruction = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("d"), naturals),
                new Formula.BoundVariable(FormulaIdentifier.Create("x"), reals),
                new Formula.BoundVariable(FormulaIdentifier.Create("L"), reals),
                new Formula.BoundVariable(FormulaIdentifier.Create("R"), reals),
            ],
            new Formula.Logic(
                constructionAssumptions,
                FormulaLogicOperator.Implies,
                TypedGap(d, x, leftArm, rightArm)));

        var tribonacciConstant = Id("beta3");
        var tribonacciPoint = Id("tribonacciChampionPoint");
        var fourChampionPoint = Id("dbonacciFourChampionPoint");
        var fiveChampionPoint = Id("dbonacciFiveChampionPoint");
        var tribonacciLargeArm = new Formula.Fraction(
            Subtract(new Formula.Power(tribonacciConstant, Num(2)), tribonacciConstant),
            Num(2));
        var tribonacciLowArm = new Formula.Fraction(
            Subtract(
                Num(1),
                new Formula.Power(tribonacciConstant, Subtract(Num(0), Num(1)))),
            Num(2));
        var threeInstance = TypedGap(
            Num(3),
            tribonacciPoint,
            tribonacciLargeArm,
            tribonacciLowArm);
        var fourInstance = TypedGap(
            Num(4),
            fourChampionPoint,
            StandardLargeArm(Num(4)),
            StandardLowArm(Num(4)));
        var fiveInstance = TypedGap(
            Num(5),
            fiveChampionPoint,
            StandardLargeArm(Num(5)),
            StandardLowArm(Num(5)));
        var fourReproof = Call(
            "IsDBonacciOrbitGap",
            Num(4),
            Num(4),
            fourChampionPoint,
            Num(3),
            StandardLargeArm(Num(4)),
            StandardLowArm(Num(4)));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The diagonal d-bonacci layer admits one uniform typed top-gap base construction.",
            H("Uniform D-Bonacci Base Gap"),
            Blocks(
                Paragraph(Text(
                    "The construction replaces order-by-order cardinality calculations and "
                    + "bounded-name recursion with two diagonal facts: the layer has 2^d-1 "
                    + "names, and its first two indexed values are zero and beta_d to the "
                    + "minus d. The point and complementary-arm equations remain explicit "
                    + "scalar hypotheses.")),
                Describe.Lean(
                    DescribeId.Create("diagonal-d-bonacci-cardinality"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/UniformBaseGap."
                        + "dbonacci_diagonal_cardinality"),
                    H("Diagonal cardinality has a closed form"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(diagonalCardinality)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "At Q=d the d-bonacci recurrence still sees only its binary initial "
                        + "segment, so the cardinality is the geometric sum 2^d-1."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("diagonal-first-index-is-zero"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/UniformBaseGap."
                        + "diagonal_first_index_zero"),
                    H("The first diagonal value is zero"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(firstZero)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The bounded-run indexing recursion sends index zero through its lower "
                        + "branch at every level and hence evaluates to zero."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("diagonal-second-index-is-the-last-place-value"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/UniformBaseGap."
                        + "diagonal_first_index_one"),
                    H("The second diagonal value is beta to the minus d"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(firstOne)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "A uniform induction through the bounded-name recursion keeps index one "
                        + "in the lower branch until its unique final occupied digit."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("uniform-diagonal-top-base-gap"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/UniformBaseGap."
                        + "diagonal_top_base_gap"),
                    H("Uniform typed top-gap construction"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(uniformConstruction)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For every d at least three, the gap between indices zero and one is the "
                        + "typed top letter. A point scaled from its left arm by beta_d^{-d}, "
                        + "together with complementary arms, supplies the two endpoint distances."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("tribonacci-base-gap-is-an-instance"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/UniformBaseGap."
                        + "tribonacci_champion_base_gap_typed"),
                    H("The tribonacci base gap is an instance"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(threeInstance)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The order-three champion point and its frozen coordinate-sum identity "
                        + "instantiate the uniform construction."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("four-bonacci-base-gap-is-an-instance"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/UniformBaseGap."
                        + "four_champion_base_gap_typed"),
                    H("The four-bonacci base gap is an instance"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(fourInstance)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The order-four scaled-point and arm-sum identities are the only "
                        + "order-specific inputs."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("five-bonacci-base-gap-is-an-instance"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/UniformBaseGap."
                        + "five_champion_base_gap_typed"),
                    H("The five-bonacci base gap is an instance"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(fiveInstance)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The order-five scaled-point and arm-sum identities give the third "
                        + "direct specialization of the same theorem."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("four-bonacci-base-gap-reproved"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/UniformBaseGap."
                        + "four_champion_base_gap_reproved"),
                    H("The legacy order-four base gap is recovered"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(fourReproof)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For order four the typed top letter evaluates to legacy label three. "
                        + "This converts the new uniform instance back to the original public "
                        + "statement without invoking its frozen proof."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/DBonacci/OrbitAlgebra")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/DBonacciGeneral/FiveChampionOrbit")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Tribonacci/ChampionOrbit")),
            ]));
    }
}
