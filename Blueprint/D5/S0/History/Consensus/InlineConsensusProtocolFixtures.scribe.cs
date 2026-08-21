using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Consensus;

internal sealed class InlineConsensusProtocolFixturesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Named fixtures exercise the fail-closed protocol and are consumed by one aggregate theorem.",
        H("Inline Consensus Protocol Fixtures"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("required-inline-consensus-fixtures-are-aggregate-pinned"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusProtocolFixtures."
                    + "required_fixture_suite_is_pinned"),
                H("Required fixtures are aggregate-pinned"),
                StatementSource.FromAuthor(Disp(F.Id("RequiredFixtureSuite"))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "RequiredFixtureSuite consumes every public fixture theorem in both Lean modules "
                        + "by name: core stage, priority, disclosure, wiring, Boolean correspondence, "
                        + "optimality, and bounded-run theorems; carrier selection, carrier-indexed "
                        + "completion, termination competitors and rows, "
                        + "all four design rows, review routing, shared budgets, thinking abstention, "
                        + "unavailable-isolation negatives, termination evaluation cost, unauthorized "
                        + "budget rejection, and all-reject review retention.")),
                    Paragraph(Text(
                        "ClauseObject is a total ten-case index from model clause identifiers to those "
                        + "named internal objects. It does not prove that the objects correspond to the "
                        + "external sshx prose; that relationship remains only the digest-pinned snapshot "
                        + "claim in Inline Consensus Optimality."))),
                DescribeRole.Theorem))));
}
