using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodicEight;

internal sealed class EnumerationEightDistinctDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var states = Id("tribonacciPeriodEightNewPhaseStateList");
        var nodup = Call("Nodup", states);

        return DocumentDefinition.Create(ScribeNode.Create(
            "The one hundred twenty new Tribonacci period-eight phase codes are duplicate-free.",
            H("Tribonacci Period-Eight Distinctness"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("all-one-hundred-twenty-new-phase-codes-are-distinct"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightDistinct."
                            + "tribonacci_new_periodic_orbit_state_codes_nodup_eight"),
                    H("All one hundred twenty new phase codes are distinct"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(nodup)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Three five-orbit blocks and three cross-block comparisons replace one "
                            + "monolithic separation computation."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightData")),
            ]));
    }
}
