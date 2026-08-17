using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.GoldenPeriodicTwelve;

internal sealed class EnumerationTwelveDisjointADocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var oldStates = Call(
            "flatMap",
            Id("goldenOrbitStates"),
            Id("goldenPeriodicOrbitRepresentativesEleven"));
        var orbitAStates = Call(
            "goldenOrbitStates",
            Id("goldenPeriodTwelveOrbitA"));
        var disjoint = Call("Disjoint", oldStates, orbitAStates);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Primitive period-twelve orbits A through M are separated from earlier states.",
            H("First Period-Twelve Separation Certificates"),
            Blocks(
                Paragraph(Text(
                    "The first thirteen new cycles are checked against all exact state "
                        + "codes enumerated through period eleven.")),
                Describe.Lean(
                    DescribeId.Create("period-twelve-orbit-a-is-new"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveDisjointA."
                            + "golden_old_new_periodic_orbit_state_codes_disjoint_a_twelve"),
                    H("Period-twelve orbit A is disjoint from earlier states"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(disjoint)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "No phase code on orbit A occurs in the complete enumeration "
                            + "through period eleven."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create(
                        "D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveDistinct")),
            ]));
    }
}
