using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodic;

internal sealed class EnumerationSixDisjointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var oldStates = Id("tribonacciEnumeratedOrbitStatesFiveList");
        var newStates = Id("tribonacciEnumeratedOrbitStatesExactlySixList");
        var disjoint = Call("Disjoint", oldStates, newStates);
        var allStates = Id("tribonacciEnumeratedOrbitStatesSixList");
        var nodup = Call("Nodup", allStates);

        return DocumentDefinition.Create(ScribeNode.Create(
            "The old and new Tribonacci phase codes form one duplicate-free period-six list.",
            H("Tribonacci Period-Six Separation"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("old-and-new-phase-codes-are-disjoint"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodic/EnumerationSixDisjoint."
                            + "tribonacci_old_new_periodic_orbit_state_codes_disjoint_six"),
                    H("Old and new phase codes are disjoint"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(disjoint)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Three bounded exact comparisons separate each new orbit from the "
                            + "thirty-seven previously certified phase states."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("all-period-six-phase-codes-are-distinct"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodic/EnumerationSixDisjoint."
                            + "tribonacci_periodic_orbit_state_codes_nodup_six"),
                    H("All period-six phase codes are distinct"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(nodup)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Prior distinctness, new distinctness, and old-new separation combine "
                            + "without re-expanding a monolithic comparison."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodic/EnumerationSixData")),
            ]));
    }
}
