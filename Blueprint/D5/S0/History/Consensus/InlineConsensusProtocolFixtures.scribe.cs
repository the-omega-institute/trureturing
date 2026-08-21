using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Consensus;

internal sealed class InlineConsensusProtocolFixturesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Named fixtures exercise the fail-closed inline-consensus protocol and are consumed by one aggregate theorem.",
        H("Inline Consensus Protocol Fixtures"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("required-inline-consensus-fixtures-are-aggregate-pinned"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusProtocolFixtures."
                    + "required_fixture_suite_is_pinned"),
                H("Required fixtures are aggregate-pinned"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The conjunction consumes the termination rows, both competitor witnesses, "
                    + "all five completion failures, forbidden-proxy rejection, the correlated-prior "
                    + "countermodel, carrier-selection rows, the review truth table, fixed role-cardinality "
                    + "checks, all-reject review routing, unauthorized-budget rejection, and the "
                    + "unavailable-isolation execution and finish prohibition. It pins internal model "
                    + "behavior only; correspondence to the external sshx prose remains the "
                    + "digest-pinned snapshot claim in Inline Consensus Optimality."))),
                DescribeRole.Theorem))));
}
