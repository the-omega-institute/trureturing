using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.GoldenPeriodicTwelve;

internal sealed class EnumerationTwelveDisjointBDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var oldStates = Call(
            "flatMap",
            Id("goldenOrbitStates"),
            Id("goldenPeriodicOrbitRepresentativesEleven"));
        var newStates = Call(
            "flatMap",
            Id("goldenOrbitStates"),
            Id("goldenPeriodicOrbitRepresentativesExactlyTwelve"));
        var disjoint = Call("Disjoint", oldStates, newStates);

        return DocumentDefinition.Create(ScribeNode.Create(
            "All primitive period-twelve states are separated from every earlier state.",
            H("Period-Twelve Separation From Earlier Periods"),
            Blocks(
                Paragraph(Text(
                    "The twelve remaining cycles are checked and combined with the first "
                        + "thirteen separation certificates.")),
                Describe.Lean(
                    DescribeId.Create("period-twelve-states-are-disjoint-from-earlier-periods"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveDisjointB."
                            + "golden_old_new_periodic_orbit_state_codes_disjoint_twelve"),
                    H("New states are disjoint from all earlier states"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(disjoint)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "No exact phase code on a primitive twelve-cycle occurs on an orbit "
                            + "enumerated through period eleven."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create(
                        "D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveDisjointA")),
            ]));
    }
}
