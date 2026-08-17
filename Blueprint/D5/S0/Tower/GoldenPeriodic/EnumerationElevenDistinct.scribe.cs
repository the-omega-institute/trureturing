using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.GoldenPeriodic;

internal sealed class EnumerationElevenDistinctDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var representatives = Id("goldenPeriodicOrbitRepresentativesExactlyEleven");
        var nodup = Call(
            "Nodup",
            Call("flatMap", Id("goldenOrbitStates"), representatives));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The 198 new period-eleven state codes are pairwise distinct.",
            H("Distinct Period-Eleven State Codes"),
            Blocks(
                Paragraph(Text(
                    "Four bounded orbit groups are checked internally and pairwise before "
                        + "their state lists are recombined.")),
                Describe.Lean(
                    DescribeId.Create("one-hundred-ninety-eight-new-state-codes-are-distinct"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenPeriodic/EnumerationElevenDistinct."
                            + "golden_new_periodic_orbit_state_codes_nodup_eleven"),
                    H("The 198 new state codes are distinct"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(nodup)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Flattening the eighteen exact eleven-cycles introduces no repeated "
                            + "quadratic state code."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/GoldenPeriodic/EnumerationElevenData")),
            ]));
    }
}
