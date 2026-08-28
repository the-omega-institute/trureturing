using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Control;

internal sealed class FiniteHorizonReachabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite winning stages exactly characterize strategies that force the goal "
            + "within the stated transition bound.",
        H("Finite-Horizon Reachability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-horizon-reachability"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Control/FiniteHorizonReachability."
                        + "finite_horizon_reachability"),
                H("Winning-stage membership is bounded strategic reachability"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At each state, the control system provides a type of available actions. "
                            + "Each action has a nonempty set of possible successor states, so the "
                            + "environment may choose any successor after the action is selected.")),
                    Paragraph(Text(
                        "The controlled predecessor of a target contains exactly the states with "
                            + "an action whose every possible successor lies in that target. The "
                            + "winning stages start at the goal and repeatedly adjoin this predecessor.")),
                    Paragraph(Text(
                        "Independently, a bounded strategy is an inductive certificate. It either "
                            + "records that the current state is already in the goal or selects an "
                            + "action and provides a continuation certificate for every successor.")),
                    Paragraph(Text(
                        "Induction on the horizon translates stage membership into this strategy "
                            + "certificate and back. Repository, pinned-library, Loogle, and "
                            + "LeanSearch checks found no exact theorem to reuse."))),
                DescribeRole.Theorem))));

    private static Formula At(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Sub(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X"), state = F.Id("x"), next = F.Id("y");
        Formula action = F.Id("u"), actions = F.Id("U"), successor = F.Id("R");
        Formula target = F.Id("S"), goal = F.Id("G"), horizon = F.Id("n");
        Formula winning = F.Id("W");
        Formula successorSet = Sub(successor, action);
        Formula controlledPredecessor = Seq(
            Call("CPre", target), Sp, Eq, Sp,
            OpenBrace, state, Sp, Colon, Sp, Exists, Sp,
            action, Sp, InMacro, Sp, At(actions, state), Comma, Sp,
            successorSet, Sp, Subseteq, Sp, target, CloseBrace);
        Formula stages = Seq(
            Sub(winning, D(0)), Sp, Eq, Sp, goal, Comma, Sp,
            Sub(winning, Seq(horizon, Plus, D(1))), Sp, Eq, Sp,
            Call("union", Sub(winning, horizon),
                Call("CPre", Sub(winning, horizon))));
        Formula result = Seq(
            state, Sp, InMacro, Sp, Sub(winning, horizon), Sp, Iff, Sp,
            Call("BoundedReachStrategy", successor, goal, horizon, state));

        return Disp(Seq(
            Forall, Sp, stateType, Colon, Sp, F.Id("Type"), Comma, Sp,
            actions, Colon, Sp, stateType, Sp, To, Sp, F.Id("Type"), Comma,
            RowBreak, Grp(),
            goal, Colon, Sp, Call("Set", stateType), Comma, Sp,
            winning, Colon, Sp, new Formula.TypeArrow(F.Id("Nat"), Call("Set", stateType)),
            Comma, RowBreak, Grp(),
            successor, Colon, Sp, Forall, Sp, state, Comma, Sp,
            At(actions, state), Sp, To, Sp, Call("Set", stateType), Comma, Sp,
            Forall, Sp, state, Comma, Sp, action, Sp, InMacro, Sp,
            At(actions, state), Comma, Sp,
            successorSet, Sp, Neq, Sp, Emptyset, Comma, RowBreak, Grp(),
            controlledPredecessor, Comma, RowBreak, Grp(),
            stages, Comma, RowBreak, Grp(),
            Forall, Sp, horizon, Comma, Sp, state, Comma, Sp,
            result, Dot));
    }
}
