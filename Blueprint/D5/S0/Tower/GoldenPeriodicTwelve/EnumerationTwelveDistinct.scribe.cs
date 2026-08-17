using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.GoldenPeriodicTwelve;

internal sealed class EnumerationTwelveDistinctDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var representatives = Id("goldenPeriodicOrbitRepresentativesExactlyTwelve");
        var nodup = Call(
            "Nodup",
            Call("flatMap", Id("goldenOrbitStates"), representatives));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The 300 new period-twelve state codes are pairwise distinct.",
            H("Distinct Period-Twelve State Codes"),
            Blocks(
                Paragraph(Text(
                    "Seven bounded orbit groups are checked internally and pairwise before "
                        + "their state lists are recombined.")),
                Describe.Lean(
                    DescribeId.Create("three-hundred-new-state-codes-are-distinct"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveDistinct."
                            + "golden_new_periodic_orbit_state_codes_nodup_twelve"),
                    H("The 300 new state codes are distinct"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(nodup)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Flattening the twenty-five exact twelve-cycles introduces no "
                            + "repeated quadratic state code."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create(
                        "D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelveData")),
            ]));
    }
}
