using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodic;

internal sealed class EnumerationSevenDistinctDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var states = Id("tribonacciPeriodSevenPhaseStateList");
        var nodup = Call("Nodup", states);

        return DocumentDefinition.Create(ScribeNode.Create(
            "The seventy new Tribonacci period-seven phase codes are duplicate-free.",
            H("Tribonacci Period-Seven Distinctness"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("all-seventy-new-phase-codes-are-distinct"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodic/EnumerationSevenDistinct."
                            + "tribonacci_new_periodic_orbit_state_codes_nodup_seven"),
                    H("All seventy new phase codes are distinct"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(nodup)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Two five-orbit blocks and five isolated cross-block comparisons "
                            + "replace one monolithic separation computation."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodic/EnumerationSevenData")),
            ]));
    }
}
