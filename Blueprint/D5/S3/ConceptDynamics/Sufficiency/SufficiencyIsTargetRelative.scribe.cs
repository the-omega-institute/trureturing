using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Sufficiency;

internal sealed class SufficiencyIsTargetRelativeDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Sufficiency/SufficiencyIsTargetRelative.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sufficiency is relative to a target family: three concrete upgrades defeat "
            + "interfaces sufficient for their coarser targets, while finite-state future "
            + "windows are recorded to stabilize.",
        H("Sufficiency Is Target-Relative"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("decision-sufficiency-does-not-recover-the-payoff-profile"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "decision_target_sufficient_but_payoff_profile_not"),
                H("Decision sufficiency does not recover the payoff profile"),
                StatementSource.FromAuthor(DecisionWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The state space is the four-element product Fin(2) times Fin(2). "
                            + "Both the interface and the decision target read the first "
                            + "coordinate, so the target is constant on every interface fiber.")),
                    Paragraph(Text(
                        "The complete payoff profile is the identity readout. The states "
                            + "(0, 0) and (0, 1) have the same interface value but different "
                            + "profiles, so the same interface is not sufficient for that "
                            + "strictly richer target."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create(
                    "interventional-marginals-do-not-recover-counterfactual-joints"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "interventional_marginal_sufficient_but_counterfactual_joint_not"),
                H("Interventional marginals do not recover counterfactual joints"),
                StatementSource.FromAuthor(CounterfactualWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For deterministic Boolean structural causal models, the interface "
                            + "is the table of single-world interventional outcome counts. "
                            + "It is sufficient for that same marginal target by fiber "
                            + "constancy.")),
                    Paragraph(Text(
                        "The existing strict-kernel witness supplies two concrete models with "
                            + "equal interventional tables but unequal unit-level counterfactual "
                            + "tables. Hence the interface is not sufficient for the cross-world "
                            + "joint target."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("every-finite-prefix-omits-some-future"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "finite_window_sufficient_but_all_future_not"),
                H("Every finite prefix omits some future"),
                StatementSource.FromAuthor(FutureWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The state is an infinite Boolean stream. For each natural horizon n, "
                            + "the interface records times zero through n and is sufficient for "
                            + "that finite-prefix target, including when n is zero.")),
                    Paragraph(Text(
                        "A constantly false stream and a stream with one pulse at time n + 1 "
                            + "have the same observed prefix but different complete futures. "
                            + "Thus every fixed finite interface in the family fails for the "
                            + "all-future target."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-state-future-windows-stabilize"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "finite_state_windows_stabilize"),
                H("Finite-state future windows stabilize"),
                StatementSource.FromAuthor(FiniteStateBoundaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every finite state carrier, arbitrary update, and arbitrary "
                            + "readout, the finite-future relation at the canonical stability "
                            + "depth equals the relation of agreement at every future time.")),
                    Paragraph(Text(
                        "This reused stabilization theorem explains why the preceding witness "
                            + "uses an infinite state space. Its statement also covers empty and "
                            + "singleton carriers, identity updates, and constant readouts."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("finite-state-is-necessary-for-window-stabilization"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "finite_state_hypothesis_is_necessary"),
                H("Finite state is necessary for window stabilization"),
                StatementSource.FromAuthor(FiniteStateNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On the state space of infinite Boolean streams, update by left shift "
                            + "and observe the head. At any finite depth n, the zero stream and "
                            + "a stream pulsing first at n + 1 remain equivalent.")),
                    Paragraph(Text(
                        "Their all-future observations differ at that next time. Therefore no "
                            + "finite relation reaches the all-future relation in this system; "
                            + "combining strictness with finite-state stabilization proves that "
                            + "the stream carrier is not finite."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("sufficiency-is-relative-to-the-target-family"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "sufficiency_is_target_relative"),
                H("Sufficiency is relative to the target family"),
                StatementSource.FromAuthor(SummaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The three witnesses are conjoined. They respectively upgrade a decision "
                            + "target to a complete payoff profile, interventional marginals to a "
                            + "counterfactual joint, and a fixed finite prefix to the complete "
                            + "future.")),
                    Paragraph(Text(
                        "Each upgrade invalidates an interface that is sufficient for the "
                            + "coarser target. Sufficiency must therefore carry an explicit target "
                            + "family rather than functioning as an unsubscripted property."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Named(Formula identifier) =>
        Seq(Operatorname, Grp(identifier));

    private static Formula TypeUniverse() =>
        Named(F.Id("Type"));

    private static Formula DecisionWitnessFormula()
    {
        Formula finTwo = Call("Fin", D(2));
        Formula state = Seq(finTwo, Sp, Times, Sp, finTwo);
        Formula decision = F.Id("qDec");
        Formula payoff = F.Id("TPay");
        Formula first = Named(F.Id("fst"));
        Formula identity = Named(F.Id("id"));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Typed(decision, Arrow(state, finTwo)), Sp, Eq, Sp, first,
            Comma, RowBreak, Grp(),
            Typed(payoff, Arrow(state, state)), Sp, Eq, Sp, identity,
            Comma, RowBreak, Grp(),
            Call("Refines", Call("canonicalTargetReadout", decision), decision),
            Sp, Land, RowBreak, Grp(),
            Neg, Sp, Call("Refines", Call("canonicalTargetReadout", payoff), decision), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula CounterfactualWitnessFormula()
    {
        Formula marginal = F.Id("Int");
        Formula joint = F.Id("CF");

        return Disp(Seq(
            Call("Refines", Call("canonicalTargetReadout", marginal), marginal),
            Sp, Land, RowBreak, Grp(),
            Neg, Sp, Call("Refines", Call("canonicalTargetReadout", joint), marginal), Dot));
    }

    private static Formula FutureWitnessFormula()
    {
        Formula horizon = F.Id("n");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula window = Call("finiteFutureWindow", horizon);
        Formula future = F.Id("fullFuture");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(horizon, naturals), Comma, RowBreak, Grp(),
            Call("Refines", Call("canonicalTargetReadout", window), window),
            Sp, Land, RowBreak, Grp(),
            Neg, Sp, Call("Refines", Call("canonicalTargetReadout", future), window), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula FiniteStateBoundaryFormula()
    {
        Formula state = F.Id("X");
        Formula output = F.Id("O");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula depth = Call("observationStabilityDepth", update, readout);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(Seq(state, Comma, Sp, output), TypeUniverse()),
            Comma, RowBreak, Grp(),
            Call("Finite", state), Comma, Sp,
            Typed(update, Arrow(state, state)), Comma, Sp,
            Typed(readout, Arrow(state, output)), Comma, RowBreak, Grp(),
            Call("finiteFutureRelation", update, readout, depth),
            Sp, Eq, Sp, Call("infiniteFutureRelation", update, readout), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula SummaryFormula()
    {
        Formula decisionTarget = F.Id("decisionTarget");
        Formula decisionInterface = F.Id("decisionInterface");
        Formula payoff = F.Id("payoffProfile");
        Formula marginal = F.Id("interventionMarginal");
        Formula joint = F.Id("counterfactualJoint");
        Formula horizon = F.Id("n");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula window = Call("finiteFutureWindow", horizon);
        Formula full = F.Id("fullFuture");
        Formula decision = Seq(
            Call(
                "Refines",
                Call("canonicalTargetReadout", decisionTarget),
                decisionInterface),
            Sp, Land, Sp,
            Neg, Sp, Call(
                "Refines",
                Call("canonicalTargetReadout", payoff),
                decisionInterface));
        Formula causal = Seq(
            Call("Refines", Call("canonicalTargetReadout", marginal), marginal),
            Sp, Land, Sp,
            Neg, Sp, Call("Refines", Call("canonicalTargetReadout", joint), marginal));
        Formula future = Seq(
            Forall, Sp, Typed(horizon, naturals), Comma, Sp,
            Call("Refines", Call("canonicalTargetReadout", window), window),
            Sp, Land, Sp,
            Neg, Sp, Call("Refines", Call("canonicalTargetReadout", full), window));

        return Disp(Seq(
            Open, decision, Close, Sp, Land, RowBreak, Grp(),
            Open, causal, Close, Sp, Land, RowBreak, Grp(),
            Open, future, Close, Dot));
    }

    private static Formula FiniteStateNecessityFormula()
    {
        Formula state = F.Id("InfiniteFuture");
        Formula horizon = F.Id("n");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula update = F.Id("streamShift");
        Formula readout = F.Id("streamHead");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Neg, Sp, Call("Finite", state), Sp, Land, RowBreak, Grp(),
            Forall, Sp, Typed(horizon, naturals), Comma, RowBreak, Grp(),
            Call("finiteFutureRelation", update, readout, horizon),
            Sp, Neq, Sp, Call("infiniteFutureRelation", update, readout), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
