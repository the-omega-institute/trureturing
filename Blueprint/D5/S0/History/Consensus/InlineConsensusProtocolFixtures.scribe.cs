using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Consensus;

internal sealed class InlineConsensusProtocolFixturesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Router-ready design, review, and termination states admit routed protocol transitions.",
        H("Inline Consensus Protocol Fixtures"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("router-transitions-are-exhaustive"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusProtocolFixtures."
                    + "router_transitions_are_exhaustive"),
                H("Router-ready states admit routed transitions"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Forall, Sp, F.Id("config"), Comma, Sp, F.Id("state"), Comma, Sp,
                    F.Id("situation"), Comma, Esc,
                    Call("DesignRouterReady", F.Id("config"), F.Id("state"), F.Id("situation")),
                    Sp, Rightarrow, Sp,
                    Call("Nonempty",
                        Call("DesignRouteTransition", F.Id("config"), F.Id("state"),
                            F.Id("situation"))), Close,
                    RowBreak, Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("config"), Comma, Sp, F.Id("state"), Comma, Sp,
                    F.Id("results"), Comma, Esc,
                    Call("ReviewRouterReady", F.Id("config"), F.Id("state"), F.Id("results")),
                    Sp, Rightarrow, Sp,
                    Call("Nonempty",
                        Call("ReviewRouteTransition", F.Id("config"), F.Id("state"),
                            F.Id("results"))), Close,
                    RowBreak, Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("config"), Comma, Sp, F.Id("state"), Comma, Sp,
                    F.Id("observation"), Comma, Esc,
                    Call("TerminationRouterReady", F.Id("config"), F.Id("state"),
                        F.Id("observation")), Sp, Rightarrow, Sp,
                    Call("Nonempty",
                        Call("TerminationRouteTransition", F.Id("config"), F.Id("state"),
                            F.Id("observation"))), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The three conjuncts are conditional on DesignRouterReady, ReviewRouterReady, "
                        + "and TerminationRouterReady respectively. Under those hypotheses the theorem "
                        + "constructs a nonempty DesignRouteTransition, ReviewRouteTransition, or "
                        + "TerminationRouteTransition for the supplied situation, results, or "
                        + "observation.")),
                    Paragraph(Text(
                        "Each transition contains a ProtocolStep, and the review and termination "
                        + "transitions record an output equal to the corresponding router result. "
                        + "The proposition makes no transition claim for an arbitrary state that does "
                        + "not satisfy the relevant readiness structure."))),
                DescribeRole.Theorem))));
}
