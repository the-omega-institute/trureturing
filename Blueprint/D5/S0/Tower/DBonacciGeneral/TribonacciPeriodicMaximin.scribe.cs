using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.DBonacciGeneral;

internal sealed class TribonacciPeriodicMaximinDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var t = Id("t");
        var championValue = Call("championValue", t);
        var championOrbit = Id("tribonacciChampionPeriodicOrbit");
        var representatives = Id("tribonacciPeriodicOrbitRepresentativesFive");
        var minima = Id("tribonacciPeriodicOrbitMinimaFive");

        var lowArmsBounded = Call(
            "selectedLowArmsBoundedBy",
            representatives,
            championValue);
        var largeCoordinate = new Formula.Fraction(
            Subtract(new Formula.Power(t, Num(2)), t),
            Num(2));
        var combinedCoordinate = new Formula.Fraction(
            Subtract(t, Num(1)),
            Num(2));
        var decodedChampion = Equal(
            Call("decodedOrbitStates", championOrbit),
            Call(
                "list",
                Call("state", Id("large"), largeCoordinate),
                Call("state", Id("combined"), combinedCoordinate)));
        var championMinimum = Call(
            "TribonacciOrbitMinimum",
            championOrbit,
            championValue);
        var maximin = Call("IsGreatest", minima, championValue);

        return DocumentDefinition.Create(ScribeNode.Create(
            "The complete period-at-most-five enumeration has maximin championValue(t), attained by the period-two ba cycle.",
            H("Tribonacci Periodic Maximin"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("every-cycle-has-a-low-arm-below-the-champion"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicMaximin."
                            + "tribonacci_periodic_orbit_low_arms_bounded"),
                    H("Every cycle has a low arm below the champion"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(lowArmsBounded)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "A selected state on each of the ten cycles has arm at most the frozen "
                            + "value. All comparisons are exact consequences of the cubic."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("the-champion-cycle-is-ba"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicMaximin."
                            + "tribonacci_champion_decoded_orbit_states"),
                    H("The champion representative is the ba cycle"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(decodedChampion)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The large-right and combined-left branches decode to the two phase "
                            + "states of the repeating ba itinerary."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("the-ba-cycle-attains-the-frozen-value"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicMaximin."
                            + "tribonacci_champion_periodic_orbit_minimum"),
                    H("The ba cycle attains the frozen value"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(championMinimum)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Both phase arms are bounded below by championValue(t), and the large "
                            + "phase attains (1 - t inverse) / 2 exactly."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("periodic-maximin-through-five"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicMaximin."
                            + "tribonacci_periodic_orbit_maximin_five"),
                    H("The periodic maximin through five"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(maximin)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Every enumerated orbit minimum is at most the champion value, while "
                            + "the period-two ba orbit belongs to the finite family and attains it."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create(
                        "D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicCompleteness")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/DBonacciGeneral/ChampionValue")),
            ]));
    }
}
