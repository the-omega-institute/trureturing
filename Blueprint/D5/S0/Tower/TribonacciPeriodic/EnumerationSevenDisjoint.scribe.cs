using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodic;

internal sealed class EnumerationSevenDisjointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var oldStates = Id("tribonacciPhaseStatesThroughSix");
        var newStates = Id("tribonacciPhaseStatesExactlySeven");
        var allStates = Id("tribonacciPhaseStatesThroughSeven");
        var disjoint = Call("Disjoint", oldStates, newStates);
        var nodup = Call("Nodup", allStates);

        return DocumentDefinition.Create(ScribeNode.Create(
            "The old and new Tribonacci phase codes form one duplicate-free period-seven list.",
            H("Tribonacci Period-Seven Separation"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("old-and-new-period-seven-phase-codes-are-disjoint"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodic/EnumerationSevenDisjoint."
                            + "tribonacci_old_new_periodic_orbit_state_codes_disjoint_seven"),
                    H("Old and new period-seven phase codes are disjoint"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(disjoint)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Ten isolated comparisons combine the two historical levels without "
                            + "re-expanding one monolithic sixty-seven-by-seventy check."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("all-phase-codes-through-seven-are-distinct"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodic/EnumerationSevenDisjoint."
                            + "tribonacci_periodic_orbit_state_codes_nodup_seven"),
                    H("All phase codes through seven are distinct"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(nodup)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The prior sixty-seven phases and seventy new phases combine into a "
                            + "duplicate-free cumulative list."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodic/EnumerationSevenDistinct")),
            ]));
    }
}
