using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.Champions;

internal sealed class GoldenAsymptoticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var k = Id("k");
        var q = Id("Q");
        var phi = Id("phi");
        var naturals = Id("N");
        var half = new Formula.Fraction(Num(1), Num(2));
        var minusOne = Subtract(Num(0), Num(1));
        var minusTwo = Subtract(Num(0), Num(2));
        var inversePhi = new Formula.Power(phi, minusOne);
        var inversePhiSquared = new Formula.Power(phi, minusTwo);
        var lowArm = new Formula.Fraction(inversePhiSquared, Num(2));
        var inverseArm = new Formula.Fraction(inversePhi, Num(2));
        var champion = Subtract(
            new Formula.Fraction(Num(13), Num(2)),
            Multiply(Num(4), phi));

        Formula Level(Formula offset) => Add(Multiply(Num(3), k), offset);

        Formula Survivor(Formula level) => Call("goldenSurvivor", level, champion);

        Formula OrbitGap(Formula level, Formula leftArm, Formula rightArm) =>
            Call("IsGoldenOrbitGap", level, champion, leftArm, rightArm);

        Formula ForAllK(Formula body) => new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("k"),
            naturals,
            body);

        var valueIdentity = Equal(
            new Formula.Fraction(Subtract(Num(2), phi), Num(2)),
            lowArm);
        var orbit = ForAllK(new Formula.Logic(
            OrbitGap(Level(Num(6)), half, half),
            FormulaLogicOperator.And,
            new Formula.Logic(
                OrbitGap(
                    Level(Num(7)),
                    new Formula.Fraction(phi, Num(2)),
                    lowArm),
                FormulaLogicOperator.And,
                OrbitGap(Level(Num(8)), inverseArm, inverseArm))));
        var armRing = ForAllK(new Formula.Logic(
            Equal(Survivor(Level(Num(6))), half),
            FormulaLogicOperator.And,
            new Formula.Logic(
                Equal(Survivor(Level(Num(7))), lowArm),
                FormulaLogicOperator.And,
                Equal(Survivor(Level(Num(8))), inverseArm))));
        var liminf = Equal(
            Call("liminfAtTop", Call("goldenSurvivor", q, champion)),
            lowArm);

        return DocumentDefinition.Create(ScribeNode.Create(
            "The golden champion follows a three-phase gap orbit with exact liminf arm.",
            H("Golden Asymptotic Champion"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("golden-asymptotic-value-identity"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/GoldenAsymptotic."
                        + "golden_asymptotic_value_identity"),
                    H("The two exact champion values agree"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(valueIdentity)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The quadratic golden-ratio identity proves directly that "
                        + "(2-phi)/2 equals phi inverse squared divided by two."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("golden-champion-three-phase-gap-orbit"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/GoldenAsymptotic."
                        + "golden_champion_gap_orbit"),
                    H("The containing gap has period three"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(orbit)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Starting at level six, refinement follows a large midpoint, "
                        + "a large gap at coordinate phi/2, and a small midpoint. "
                        + "The frozen golden substitution sends these states cyclically "
                        + "as L, L, S."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("golden-champion-three-phase-arm-ring"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/GoldenAsymptotic."
                        + "golden_champion_arm_ring"),
                    H("The three exact arm phases"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(armRing)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The phase-a declaration gives the level 3k+6 value one half. "
                            + "Its companion phase-b and phase-c theorems give respectively "
                            + "phi inverse squared over two and phi inverse over two.")),
                        Paragraph(Text(
                            "The separate level-five theorem verifies the single-step "
                            + "in-hull preimage and also has arm phi inverse over two."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("golden-champion-liminf-arm"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Champions/GoldenAsymptotic."
                        + "golden_champion_liminf"),
                    H("The champion liminf arm"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(liminf)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "All tail phases are at least phi inverse squared over two, "
                            + "and the phase-b levels occur cofinally, so the along-level "
                            + "filter liminf is exactly that value.")),
                        Paragraph(Text(
                            "This is not the fixed-level supremum one half. The stronger "
                            + "global supremum over points of their liminf arms remains open "
                            + "here because the available maximizer results classify one "
                            + "level at a time, not the full backward survivor set."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/GoldenSubstitution")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/MetricGeometry/GoldenSurvivor")),
            ]));
    }
}
