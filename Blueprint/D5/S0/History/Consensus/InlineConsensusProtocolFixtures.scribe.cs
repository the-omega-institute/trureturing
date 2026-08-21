using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Consensus;

internal sealed class InlineConsensusProtocolFixturesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Router-ready states admit route-transition witnesses governed by inlineConsensusModel.",
        H("Inline Consensus Protocol Fixtures"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("router-transitions-are-exhaustive"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusProtocolFixtures."
                    + "router_transitions_are_exhaustive"),
                H("Router-ready states admit routed transitions"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("RouterTransitionsExhaustive", F.Id("inlineConsensusModel"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "RouterTransitionsExhaustive inlineConsensusModel expands to three universally "
                        + "quantified implications. DesignRouterReady, ReviewRouterReady, and "
                        + "TerminationRouterReady are each parameterized by inlineConsensusModel; under "
                        + "the corresponding readiness hypothesis, the theorem constructs a nonempty "
                        + "DesignRouteTransition, ReviewRouteTransition, or TerminationRouteTransition "
                        + "with that same model.")),
                    Paragraph(Text(
                        "Each witness contains an inlineConsensusModel.transition step. The design event "
                        + "is selected by the model's designRoute, while the review and termination "
                        + "witnesses record an output equal to the corresponding model router result. "
                        + "The proposition makes no transition claim for an arbitrary state that does "
                        + "not satisfy the relevant readiness structure, and it does not quantify over "
                        + "arbitrary models."))),
                DescribeRole.Theorem))));
}
