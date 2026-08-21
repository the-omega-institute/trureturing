using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Consensus;

internal sealed class InlineConsensusProtocolFixturesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Named protocol executions witness every design, review, and termination router exit.",
        H("Inline Consensus Protocol Fixtures"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("router-transitions-are-exhaustive"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusProtocolFixtures."
                    + "router_transitions_are_exhaustive"),
                H("Router transitions are exhaustive"),
                StatementSource.FromAuthor(Disp(F.Id("RouterTransitionsExhaustive"))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "RouterTransitionsExhaustive is the conjunction of three propositions: every "
                        + "DesignExit has a nonempty DesignRouteTransition, every ReviewExit has a "
                        + "nonempty ReviewRouteTransition, and every TerminationExit has a nonempty "
                        + "TerminationRouteTransition.")),
                    Paragraph(Text(
                        "The proof assembles named ProtocolStep fixtures for implementation, successful "
                        + "and exhausted convergence, stalled and fake-consensus design exits, repair, "
                        + "termination candidacy, user decision and repeated review, and all four "
                        + "termination exits. It proves transition-level inhabitation, not that every "
                        + "arbitrary protocol state can take every route."))),
                DescribeRole.Theorem))));
}
