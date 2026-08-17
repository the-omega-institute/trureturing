using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodic;

internal sealed class EnumerationSevenDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var newOrbits = Id("tribonacciPeriodicOrbitRepresentativesExactlySeven");
        var count = Equal(Call("length", newOrbits), Num(10));
        var valid = Call("Forall", newOrbits, Id("tribonacciCodedOrbitValid"));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Ten exact primitive cycles supply the new Tribonacci period-seven data.",
            H("Tribonacci Period-Seven Orbit Data"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("ten-new-primitive-period-seven-orbits"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodic/EnumerationSevenData."
                            + "tribonacci_new_periodic_orbit_count_seven"),
                    H("Ten new primitive period-seven orbits"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(count)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Rotation reduction of the seventy new phase states gives ten "
                            + "representatives, each with seven transitions."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("all-ten-period-seven-orbits-are-valid"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodic/EnumerationSevenData."
                            + "tribonacci_new_periodic_orbit_representatives_valid_seven"),
                    H("All ten new period-seven orbits are valid"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(valid)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Five bounded exact proof groups certify branch choices, gap bounds, "
                            + "and closure under the default resource limits."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodic/EnumerationSix")),
            ]));
    }
}
