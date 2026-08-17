using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodic;

internal sealed class EnumerationSixDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var newOrbits = Id("tribonacciPeriodicOrbitRepresentativesExactlySix");
        var newCount = Equal(Call("length", newOrbits), Num(5));
        var valid = Call("Forall", newOrbits, Id("tribonacciCodedOrbitValid"));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Five exact primitive cycles supply the new Tribonacci period-six data.",
            H("Tribonacci Period-Six Orbit Data"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("five-new-primitive-period-six-orbits"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodic/EnumerationSixData."
                            + "tribonacci_new_periodic_orbit_count_six"),
                    H("Five new primitive period-six orbits"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(newCount)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Rotation reduction of the thirty new phase states gives five "
                            + "representatives, each with six transitions."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("all-five-new-orbits-are-valid"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodic/EnumerationSixData."
                            + "tribonacci_new_periodic_orbit_representatives_valid_six"),
                    H("All five new orbits are valid"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(valid)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Exact cubic inequalities certify every branch choice, gap bound, "
                            + "and closing equation without numerical approximation."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicMaximin")),
            ]));
    }
}
