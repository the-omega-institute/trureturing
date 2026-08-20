using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciPeriodicEight;

internal sealed class EnumerationEightDisjointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var inherited = Id("tribonacciPeriodEightInheritedPhaseStates");
        var fresh = Id("tribonacciPeriodEightNewPhaseStates");
        var expected = Id("tribonacciPeriodEightExpectedPhaseStateList");
        var disjoint = Call("Disjoint", inherited, fresh);
        var nodup = Call("Nodup", expected);

        return DocumentDefinition.Create(ScribeNode.Create(
            "The eleven inherited and one hundred twenty new period-eight codes are separated.",
            H("Tribonacci Period-Eight Separation"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("inherited-and-new-period-eight-phase-codes-are-disjoint"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightDisjoint."
                            + "tribonacci_inherited_new_state_codes_disjoint_eight"),
                    H("Inherited and new period-eight phase codes are disjoint"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(disjoint)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Three isolated five-orbit comparisons keep the separation check within "
                            + "the default tactic budget."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("all-expected-period-eight-phase-codes-are-distinct"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightDisjoint."
                            + "tribonacci_period_eight_expected_state_codes_nodup"),
                    H("All expected period-eight phase codes are distinct"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(nodup)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The eleven divisor-period phases and one hundred twenty primitive phases "
                            + "combine into a duplicate-free list of one hundred thirty-one."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciPeriodicEight/EnumerationEightDistinct")),
            ]));
    }
}
