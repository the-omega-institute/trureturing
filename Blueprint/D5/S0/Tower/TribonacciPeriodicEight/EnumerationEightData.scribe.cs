using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodicEight;

internal sealed class EnumerationEightDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var newOrbits = Id("tribonacciPeriodicOrbitRepresentativesExactlyEight");
        var count = Equal(Call("length", newOrbits), Num(15));
        var valid = Call("Forall", newOrbits, Id("tribonacciCodedOrbitValid"));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Fifteen exact primitive cycles supply the new Tribonacci period-eight data.",
            H("Tribonacci Period-Eight Orbit Data"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("fifteen-new-primitive-period-eight-orbits"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightData."
                            + "tribonacci_new_periodic_orbit_count_eight"),
                    H("Fifteen new primitive period-eight orbits"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(count)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Rotation reduction of the one hundred twenty new phase states gives "
                            + "fifteen representatives, each with eight transitions."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("all-fifteen-period-eight-orbits-are-valid"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightData."
                            + "tribonacci_new_periodic_orbit_representatives_valid_eight"),
                    H("All fifteen new period-eight orbits are valid"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(valid)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Eight bounded exact proof groups certify branch choices, gap bounds, "
                            + "closure, and phase distinctness under the default limits."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodic/EnumerationSeven")),
            ]));
    }
}
