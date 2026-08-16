using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.Tribonacci;

internal sealed class TribonacciChampionOrbitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var k = Id("k");
        var q = Id("Q");
        var t = Id("t");
        var champion = Id("xc");
        var naturals = Id("N");
        var minusOne = Subtract(Num(0), Num(1));
        var minusTwo = Subtract(Num(0), Num(2));
        var inverseT = new Formula.Power(t, minusOne);
        var inverseTSquared = new Formula.Power(t, minusTwo);
        var lowArm = new Formula.Fraction(Subtract(Num(1), inverseT), Num(2));
        var middleArm = new Formula.Fraction(Subtract(t, Num(1)), Num(2));
        var largeCoordinate = new Formula.Fraction(
            Subtract(new Formula.Power(t, Num(2)), t),
            Num(2));
        var pointFormula = Equal(
            champion,
            new Formula.Fraction(Subtract(inverseT, inverseTSquared), Num(2)));

        Formula OrbitGap(Formula level, Formula leftArm, Formula rightArm) =>
            Call("IsTribonacciOrbitGap", level, champion, leftArm, rightArm);

        Formula Survivor(Formula level) => Call("tribonacciSurvivor", level, champion);

        var orbitFormula = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("k"),
            naturals,
            new Formula.Logic(
                OrbitGap(Add(Multiply(Num(2), k), Num(3)), largeCoordinate, lowArm),
                FormulaLogicOperator.And,
                OrbitGap(Add(Multiply(Num(2), k), Num(4)), middleArm, middleArm)));
        var oddArmFormula = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("k"),
            naturals,
            Equal(Survivor(Add(Multiply(Num(2), k), Num(3))), lowArm));
        var evenArmFormula = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("k"),
            naturals,
            Equal(Survivor(Add(Multiply(Num(2), k), Num(4))), middleArm));
        var liminfFormula = Equal(
            Call("liminfAtTop", Call("tribonacciSurvivor", q, champion)),
            lowArm);

        return DocumentDefinition.Create(ScribeNode.Create(
            "A closed Tribonacci period-two point has its exact liminf survivor arm.",
            H("Tribonacci Champion Orbit"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("tribonacci-period-two-point"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/ChampionOrbit.tribonacciChampionPoint"),
                    H("Closed form of the period-two point"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(pointFormula)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The selected point is one half of t inverse minus t inverse squared. "
                        + "It lies in the first level-three large gap and is reused without "
                        + "redefining the frozen Tribonacci constant."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("tribonacci-right-left-gap-orbit"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/ChampionOrbit."
                        + "tribonacci_champion_gap_orbit"),
                    H("The containing gap has period-two itinerary ba"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(orbitFormula)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "At every odd phase the point occupies a large gap with normalized "
                        + "left coordinate (t squared minus t)/2 and right arm "
                        + "(1-t inverse)/2. Refinement takes the right branch b into a "
                        + "combined gap, where the point is the midpoint; the next left "
                        + "branch a returns to the same large-gap coordinate."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("tribonacci-period-two-arm-values"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/ChampionOrbit."
                        + "tribonacci_champion_survivor_odd"),
                    H("Exact low arm on every large-gap phase"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(oddArmFormula)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The normalized distance on levels 2k+3 is exactly "
                            + "(1-t inverse)/2.")),
                        Paragraph(Text(
                            "The companion theorem tribonacci_champion_survivor_even gives "
                            + "the intervening level 2k+4 value (t-1)/2.")),
                        new DocumentBlock.DisplayFormula(FormulaDsl.Disp(evenArmFormula))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("tribonacci-period-two-liminf-arm"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/ChampionOrbit."
                        + "tribonacci_champion_liminf"),
                    H("The period-two liminf arm"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(liminfFormula)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Every tail value is at least the low phase and odd phases occur "
                            + "cofinally, so the filter liminf is exactly "
                            + "(1-t inverse)/2.")),
                        Paragraph(Text(
                            "This is an along-level liminf theorem. It neither uses the "
                            + "fixed-level one-half bound as a substitute nor claims the "
                            + "unformalized global supremum over all points."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Tribonacci/Substitution")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Tribonacci/Survivor")),
            ]));
    }
}
