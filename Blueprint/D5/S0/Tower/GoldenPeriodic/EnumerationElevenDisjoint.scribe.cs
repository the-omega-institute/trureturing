using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.GoldenPeriodic;

internal sealed class EnumerationElevenDisjointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var oldStates = Call(
            "flatMap",
            Id("goldenOrbitStates"),
            Id("goldenPeriodicOrbitRepresentativesTen"));
        var newStates = Call(
            "flatMap",
            Id("goldenOrbitStates"),
            Id("goldenPeriodicOrbitRepresentativesExactlyEleven"));
        var disjoint = Call("Disjoint", oldStates, newStates);

        return DocumentDefinition.Create(ScribeNode.Create(
            "The primitive period-eleven states do not collide with any state through ten.",
            H("Period-Eleven Separation From Earlier Periods"),
            Blocks(
                Paragraph(Text(
                    "Each new orbit is checked against the frozen period-nine states and the "
                        + "period-ten extension, then the results are recombined.")),
                Describe.Lean(
                    DescribeId.Create("period-eleven-states-are-disjoint-from-earlier-periods"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationElevenDisjoint."
                            + "golden_old_new_periodic_orbit_state_codes_disjoint_eleven"),
                    H("New states are disjoint from all earlier states"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(disjoint)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "No exact phase code on a primitive eleven-cycle occurs on an orbit "
                            + "enumerated through period ten."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/GoldenPeriodic/EnumerationElevenDistinct")),
            ]));
    }
}
