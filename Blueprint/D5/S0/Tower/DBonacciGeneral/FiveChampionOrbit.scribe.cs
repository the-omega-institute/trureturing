using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.DBonacciGeneral;

internal sealed class DBonacciGeneralFiveChampionOrbitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var k = Id("k");
        var q = Id("Q");
        var b = Id("b5");
        var champion = Id("x5");
        var naturals = Id("N");
        var minusOne = Subtract(Num(0), Num(1));
        var minusFour = Subtract(Num(0), Num(4));
        var million = Num(1000000);
        var denominator = Subtract(new Formula.Power(b, Num(2)), Num(1));
        var lowArm = new Formula.Fraction(
            Subtract(Subtract(new Formula.Power(b, Num(2)), b), Num(1)),
            denominator);
        var middleArm = new Formula.Fraction(Num(1), denominator);
        var largeArm = new Formula.Fraction(b, denominator);
        var rightMiddleArm = Multiply(b, lowArm);
        var initial = new Formula.Fraction(
            Subtract(Num(1), new Formula.Power(b, minusOne)),
            Num(2));

        Formula OrbitGap(Formula level, Formula label, Formula leftArm, Formula rightArm) =>
            Call("IsDBonacciOrbitGap", Num(5), level, champion, label, leftArm, rightArm);

        var survivor = Call("dbonacciSurvivor", Num(5), q, champion);
        var liminf = Call("liminfAtTop", survivor);
        var pointFormula = Equal(
            champion,
            new Formula.Fraction(new Formula.Power(b, minusFour), denominator));
        var orbitFormula = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("k"),
            naturals,
            new Formula.Logic(
                OrbitGap(Add(Multiply(Num(2), k), Num(5)), Num(4), largeArm, lowArm),
                FormulaLogicOperator.And,
                OrbitGap(
                    Add(Multiply(Num(2), k), Num(6)),
                    Num(3),
                    middleArm,
                    rightMiddleArm)));
        var liminfFormula = Equal(liminf, Call("championValue", b));
        var numericFormula = new Formula.Relation(
            Call(
                "abs",
                Subtract(liminf, new Formula.Fraction(Num(313794), million))),
            FormulaRelationOperator.LessThan,
            new Formula.Fraction(Num(1), million));
        var refutationFormula = NotEqual(initial, liminf);

        return DocumentDefinition.Create(ScribeNode.Create(
            "A closed five-bonacci period-two point attains the corrected champion arm.",
            H("Five-Bonacci Champion Orbit"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("five-bonacci-period-two-point"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/FiveChampionOrbit."
                        + "dbonacciFiveChampionPoint"),
                    H("Closed five-bonacci period-two point"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(pointFormula)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "With b5 the order-five Perron root, this is the real point whose tail "
                            + "digits are 1010... beginning at position six."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("five-bonacci-right-left-gap-orbit"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/FiveChampionOrbit."
                        + "five_champion_gap_orbit"),
                    H("The containing gap has label-four label-three period two"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(orbitFormula)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "At levels 2k+5 the point lies in a largest label-four gap. Its right "
                            + "refinement enters label three, and the next left refinement returns "
                            + "to label four. The proof reuses the general d-bonacci substitution "
                            + "and survivor carrier supplied by the order-four development."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("five-bonacci-period-two-liminf"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/FiveChampionOrbit."
                        + "dbonacci_five_champion_liminf"),
                    H("Exact liminf of the five-bonacci orbit"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(liminfFormula)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The even phase is exactly championValue(b5), the odd phase is the larger "
                            + "middle arm, and the low phase occurs cofinally. This proves an "
                            + "attaining orbit; it does not replace the separate all-points upper "
                            + "bound needed for a global extremality theorem."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("five-bonacci-liminf-numeric-certificate"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/FiveChampionOrbit."
                        + "dbonacci_five_champion_liminf_numeric"),
                    H("Order-five champion-arm numerical certificate"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(numericFormula)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The exact orbit liminf differs from 0.313794 by less than one millionth."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("initial-five-bonacci-orbit-formula-refuted"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/FiveChampionOrbit."
                        + "dbonacci_five_initial_formula_ne_champion_liminf"),
                    H("The initial expression fails on the five-bonacci orbit"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(refutationFormula)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The initial expression (1-b5 inverse)/2 is unequal to the exact liminf "
                            + "of this period-two point."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/DBonacci/ChampionOrbit")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/DBonacciGeneral/ChampionValue")),
            ]));
    }
}
