using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.DBonacciChampion;

internal sealed class DBonacciChampionGeneralBaOrbitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var beta = Id("beta");
        var b4 = Id("b4");
        var d = Id("d");
        var k = Id("k");
        var reals = Id("R");
        var naturals = Id("N");
        var denominator = Subtract(new Formula.Power(beta, Num(2)), Num(1));
        var fixedPoint = new Formula.Fraction(beta, denominator);
        Formula Value(Formula root) => new Formula.Fraction(
            Subtract(Subtract(new Formula.Power(root, Num(2)), root), Num(1)),
            Subtract(new Formula.Power(root, Num(2)), Num(1)));
        var baDefinition = Equal(Call("baFixedPoint", beta), fixedPoint);
        var returnFixedPoint = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("beta"),
            reals,
            new Formula.Logic(
                new Formula.Relation(Num(1), FormulaRelationOperator.LessThan, beta),
                FormulaLogicOperator.Implies,
                Equal(
                    Call("baReturn", beta, Call("baFixedPoint", beta)),
                    Call("baFixedPoint", beta))));
        var complementaryArm = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("beta"),
            reals,
            new Formula.Logic(
                new Formula.Relation(Num(1), FormulaRelationOperator.LessThan, beta),
                FormulaLogicOperator.Implies,
                Equal(
                    Call("championValue", beta),
                    Subtract(Num(1), Call("baFixedPoint", beta)))));
        var point = Call("dbonacciChampionPoint", d);
        var generalLiminf = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("d"),
            naturals,
            new Formula.Logic(
                new Formula.Relation(Num(3), FormulaRelationOperator.LessThanOrEqual, d),
                FormulaLogicOperator.Implies,
                Equal(
                    Call("liminfAtTop", Call("dbonacciSurvivor", d, Id("Q"), point)),
                    Call("championValue", Call("dbonacciPerronRoot", d)))));
        var orbit = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("d"),
            naturals,
            new Formula.Logic(
                new Formula.Relation(Num(3), FormulaRelationOperator.LessThanOrEqual, d),
                FormulaLogicOperator.Implies,
                new Formula.Bind(
                    FormulaQuantifier.ForAll,
                    FormulaIdentifier.Create("k"),
                    naturals,
                    Call("dbonacciChampionGapOrbit", d, k))));
        var fourInstance = Equal(
            Call("liminfAtTop", Call("dbonacciSurvivor", Num(4), Id("Q"),
                Call("dbonacciFourChampionPoint"))),
            Value(b4));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The universal ba fixed point closes the corrected d-bonacci champion liminf.",
            H("General D-Bonacci ba Champion"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("ba-fixed-point-formula"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciChampion/GeneralBaOrbit.baFixedPoint"),
                    H("Universal ba fixed point"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(baDefinition)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The normalized large arm fixed by the right-left ba return is beta "
                            + "over beta squared minus one."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("ba-return-fixed-point"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciChampion/GeneralBaOrbit.ba_fixed_point"),
                    H("The ba return fixes the displayed arm"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(returnFixedPoint)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For every real beta above one, the affine map beta times (beta u minus "
                            + "one) returns beta over beta squared minus one."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("corrected-value-is-complementary-arm"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciChampion/GeneralBaOrbit."
                            + "championValue_eq_one_sub_baFixedPoint"),
                    H("The corrected value is the complementary arm"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(complementaryArm)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The low arm is one minus the universal ba fixed point, yielding the "
                            + "rational champion expression."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("general-ba-period-two-orbit"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciChampion/GeneralBaOrbit."
                            + "dbonacci_champion_gap_orbit"),
                    H("Every order has the same typed ba orbit"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(orbit)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The diagonal top-gap witness and the typed substitution algebra produce "
                            + "the two alternating survivor arms at levels 2k+d and 2k+d+1."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("general-ba-liminf"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciChampion/GeneralBaOrbit.dbonacci_champion_liminf"),
                    H("The universal corrected liminf"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(generalLiminf)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For every d at least three, the exact liminf along the ba point is "
                            + "championValue of the d-bonacci Perron root."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("four-instance-from-general"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciChampion/GeneralBaOrbit."
                            + "four_champion_liminf_from_general"),
                    H("Order four is a general-theorem instance"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(fourInstance)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The corrected order-four liminf is obtained from the all-order theorem "
                            + "after identifying its closed point with the existing hand instance."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/DBonacciGeneral/ChampionValue")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/DBonacciGeneral/UniformBaseGap")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/DBonacci/ChampionOrbit")),
            ]));
    }
}
