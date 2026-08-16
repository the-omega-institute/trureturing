using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.DBonacci;

internal sealed class DBonacciChampionOrbitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var k = Id("k");
        var q = Id("Q");
        var b = Id("b4");
        var champion = Id("x4");
        var naturals = Id("N");
        var minusOne = Subtract(Num(0), Num(1));
        var minusThree = Subtract(Num(0), Num(3));
        var denominator = Subtract(new Formula.Power(b, Num(2)), Num(1));
        var lowArm = new Formula.Fraction(
            Subtract(Subtract(new Formula.Power(b, Num(2)), b), Num(1)),
            denominator);
        var middleArm = new Formula.Fraction(Num(1), denominator);
        var largeArm = new Formula.Fraction(b, denominator);
        var rightMiddleArm = Multiply(b, lowArm);
        var candidate = new Formula.Fraction(
            Subtract(Num(1), new Formula.Power(b, minusOne)),
            Num(2));

        Formula OrbitGap(Formula level, Formula label, Formula leftArm, Formula rightArm) =>
            Call("IsDBonacciOrbitGap", Num(4), level, champion, label, leftArm, rightArm);

        Formula Survivor(Formula level) =>
            Call("dbonacciSurvivor", Num(4), level, champion);

        var pointFormula = Equal(
            champion,
            new Formula.Fraction(new Formula.Power(b, minusThree), denominator));
        var orbitFormula = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("k"),
            naturals,
            new Formula.Logic(
                OrbitGap(Add(Multiply(Num(2), k), Num(4)), Num(3), largeArm, lowArm),
                FormulaLogicOperator.And,
                OrbitGap(
                    Add(Multiply(Num(2), k), Num(5)),
                    Num(2),
                    middleArm,
                    rightMiddleArm)));
        var lowPhaseFormula = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("k"),
            naturals,
            Equal(Survivor(Add(Multiply(Num(2), k), Num(4))), lowArm));
        var middlePhaseFormula = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("k"),
            naturals,
            Equal(Survivor(Add(Multiply(Num(2), k), Num(5))), middleArm));
        var liminf = Call("liminfAtTop", Call("dbonacciSurvivor", Num(4), q, champion));

        return DocumentDefinition.Create(ScribeNode.Create(
            "A closed four-bonacci period-two point has a liminf that refutes the initial formula.",
            H("Four-Bonacci Champion Orbit"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("four-bonacci-period-two-point"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/ChampionOrbit.dbonacciFourChampionPoint"),
                    H("Closed four-bonacci period-two point"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(pointFormula)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "With b4 the frozen order-four Perron root, the selected point is "
                            + "b4 inverse-cubed divided by b4 squared minus one. Direct high-precision "
                            + "grid enumeration first located this point before the closed orbit was proved."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("four-bonacci-right-left-gap-orbit"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/ChampionOrbit.four_champion_gap_orbit"),
                    H("The containing gap has label-three label-two period two"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(orbitFormula)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "At levels 2k+4 the point lies in a largest label-three gap, with "
                            + "normalized arms b4/(b4 squared minus one) and the corrected low arm. "
                            + "The right refinement enters label two; the following left refinement "
                            + "returns to label three. The proof uses the local substitution law and "
                            + "therefore retains its boundary terms."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("four-bonacci-period-two-survivor-values"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/ChampionOrbit.four_champion_survivor_even"),
                    H("Exact survivor values on both phases"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(lowPhaseFormula)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The normalized distance at every level 2k+4 is exactly "
                                + "(b4 squared minus b4 minus one)/(b4 squared minus one).")),
                        Paragraph(Text(
                            "The companion odd-level theorem gives 1/(b4 squared minus one) at "
                                + "every level 2k+5.")),
                        new DocumentBlock.DisplayFormula(FormulaDsl.Disp(middlePhaseFormula))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("four-bonacci-period-two-liminf"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/ChampionOrbit.dbonacci_four_champion_liminf"),
                    H("Exact liminf of the four-bonacci orbit"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(Equal(liminf, lowArm))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The low phase occurs cofinally and every eventual value is at least "
                                + "that phase, so the along-level filter liminf is the corrected low arm.")),
                        Paragraph(Text(
                            "This theorem concerns one fixed point as Q tends to infinity. A fixed-Q "
                                + "upper bound, or a supremum over all points, is a different quantity; "
                                + "neither is substituted for this liminf, and no global championship "
                                + "claim is made here."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("initial-four-bonacci-formula-refuted"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacci/ChampionOrbit."
                        + "dbonacci_four_initial_candidate_lt_liminf"),
                    H("The initial candidate is strictly too small at order four"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(new Formula.Relation(
                        candidate,
                        FormulaRelationOperator.LessThan,
                        liminf))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Thus (1-b4 inverse)/2 is not the four-bonacci value. The companion "
                            + "inequality theorem records explicit disequality. Agreement at orders "
                            + "two and three therefore does not establish a formula for all d."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/DBonacci/Substitution")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/DBonacci/Survivor")),
            ]));
    }
}
