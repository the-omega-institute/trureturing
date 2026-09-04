using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.VisibleDescent;

internal sealed class ThreeRuleActorDecidabilityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/VisibleDescent/ThreeRuleActorDecidability."
            + "three_rule_actor_decidability";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actor-visible desires are preserved exactly by readout-compatible transitions, "
            + "while a recipient's desire requires descent through the actor's readout.",
        H("Three Rule Forms and Actor Readout"),
        Blocks(Describe.Lean(
            DescribeId.Create("three-rule-actor-decidability"),
            DeclarationHandle.Create(Declaration),
            H("Compatibility separates actor-local and recipient-dependent rules"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The observation family may vary with the agent. The actor readout, "
                        + "mirrored transition, and actual transition are constructed from "
                        + "the displayed source primitives before any rule predicate is stated.")),
                Paragraph(Text(
                    "Compatibility preserves every desire already constant on actor-readout "
                        + "fibers. Conversely, two equal-readout states whose mirrored "
                        + "successors have different readouts define a separating desire, so "
                        + "compatibility is necessary for preservation of every such desire.")),
                Paragraph(Text(
                    "The positive rule additionally uses the actor's ability predicate. The "
                        + "structural rule uses the recipient's desire after the actual action; "
                        + "Mathlib's factorization criterion constructs its descended predicate.")),
                Paragraph(Text(
                    "Repository searches found an adjacent answerability criterion but no "
                        + "theorem with the transition converse and all three rule forms. "
                        + "Pinned Mathlib supplies the fiber-constancy and descent primitives."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("State");
        Formula actionType = F.Id("Action");
        Formula agentType = F.Id("Agent");
        Formula observation = F.Id("Observation");
        Formula readout = F.Id("readout");
        Formula transition = F.Id("transition");
        Formula desire = F.Id("desire");
        Formula ability = F.Id("ability");
        Formula action = F.Id("action");
        Formula actor = F.Id("actor");
        Formula recipient = F.Id("recipient");
        Formula agent = F.Id("agent");
        Formula state = F.Id("state");
        Formula selfDesire = F.Id("selfDesire");
        Formula descended = F.Id("descended");
        Formula q = F.Id("q");
        Formula mirrored = F.Id("mirrored");
        Formula actual = F.Id("actual");
        Formula compatible = F.Id("compatible");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula prop = Seq(Operatorname, Grp(F.Id("Prop")));
        Formula observationAtActor = Apply(observation, actor);
        Formula statePredicate = Arrow(stateType, prop);

        Formula actorDesire = Apply(desire, actor);
        Formula actorAbility = Lambda(
            Typed(state, stateType),
            Apply(ability, actor, state, action, recipient));
        Formula mirroredActorDesire = Lambda(
            Typed(state, stateType),
            Apply(desire, actor, Apply(mirrored, state)));
        Formula negativeMirroredActorDesire = Lambda(
            Typed(state, stateType),
            Negate(Apply(desire, actor, Apply(mirrored, state))));
        Formula negativeMirroredSelfDesire = Lambda(
            Typed(state, stateType),
            Negate(Apply(selfDesire, Apply(mirrored, state))));
        Formula positiveMirroredRule = Lambda(
            Typed(state, stateType),
            Seq(
                Apply(desire, actor, Apply(mirrored, state)),
                Sp, Land, Sp,
                Apply(ability, actor, state, action, recipient)));
        Formula actualRecipientDesire = Lambda(
            Typed(state, stateType),
            Apply(desire, recipient, Apply(actual, state)));
        Formula negativeActualRecipientDesire = Lambda(
            Typed(state, stateType),
            Negate(Apply(desire, recipient, Apply(actual, state))));

        Formula forward = Seq(
            Factor(actorDesire, q), Sp, Rightarrow, Sp,
            compatible, Sp, Rightarrow, Sp,
            Factor(negativeMirroredActorDesire, q));
        Formula separatingConverse = Seq(
            Negate(compatible), Sp, Rightarrow, Sp,
            Exists, Sp, Typed(selfDesire, statePredicate), Comma, Sp,
            Open,
            Factor(selfDesire, q), Sp, Land, Sp,
            Negate(Factor(negativeMirroredSelfDesire, q)),
            Close);
        Formula universalPreservation = Seq(
            Forall, Sp, Typed(selfDesire, statePredicate), Comma, Sp,
            Factor(selfDesire, q), Sp, Rightarrow, Sp,
            Factor(negativeMirroredSelfDesire, q));
        Formula universalCriterion = Seq(
            compatible, Sp, Leftrightarrow, Sp,
            Open, universalPreservation, Close);
        Formula positive = Seq(
            Factor(actorDesire, q), Sp, Rightarrow, Sp,
            Factor(actorAbility, q), Sp, Rightarrow, Sp,
            compatible, Sp, Rightarrow, Sp,
            Factor(positiveMirroredRule, q));
        Formula structural = Seq(
            Factor(negativeActualRecipientDesire, q), Sp, Leftrightarrow, Sp,
            Exists, Sp,
            Typed(descended, Arrow(observationAtActor, prop)), Comma, Sp,
            actualRecipientDesire, Sp, Eq, Sp,
            descended, Sp, Circ, Sp, q);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp,
                Typed(Seq(stateType, Comma, Sp, actionType, Comma, Sp, agentType), type),
                Comma),
            Seq(
                Typed(observation, Arrow(agentType, type)), Comma),
            Seq(
                Typed(readout, Seq(
                    Open, Typed(agent, agentType), Close, Sp, To, Sp,
                    Arrow(stateType, Apply(observation, agent)))),
                Comma),
            Seq(
                Typed(transition,
                    Arrow(stateType,
                        Arrow(actionType,
                            Arrow(agentType, Arrow(agentType, stateType))))),
                Comma),
            Seq(
                Typed(desire, Arrow(agentType, statePredicate)), Comma),
            Seq(
                Typed(ability,
                    Arrow(agentType,
                        Arrow(stateType,
                            Arrow(actionType, Arrow(agentType, prop))))),
                Comma),
            Seq(
                Typed(action, actionType), Comma, Sp,
                Typed(actor, agentType), Comma, Sp,
                Typed(recipient, agentType), Comma),
            Seq(
                Operatorname, Grp(F.Id("let")), Sp,
                q, Colon, Sp, Arrow(stateType, observationAtActor), Sp, Colon, Eq, Sp,
                Apply(readout, actor), Comma),
            Seq(
                mirrored, Colon, Sp, Arrow(stateType, stateType), Sp, Colon, Eq, Sp,
                Lambda(Typed(state, stateType),
                    Apply(transition, state, action, recipient, actor)), Comma),
            Seq(
                actual, Colon, Sp, Arrow(stateType, stateType), Sp, Colon, Eq, Sp,
                Lambda(Typed(state, stateType),
                    Apply(transition, state, action, actor, recipient)), Comma),
            Seq(
                compatible, Colon, Sp, prop, Sp, Colon, Eq, Sp,
                Factor(Seq(q, Sp, Circ, Sp, mirrored), q), Sp,
                Operatorname, Grp(F.Id("in"))),
            Seq(Open, forward, Close, Sp, Land),
            Seq(Open, separatingConverse, Close, Sp, Land),
            Seq(Open, universalCriterion, Close, Sp, Land),
            Seq(Open, positive, Close, Sp, Land),
            Seq(Open, structural, Close, Dot),
        ]));
    }

    private static Formula Factor(Formula function, Formula through) =>
        Call("FactorsThrough", function, through);

    private static Formula Negate(Formula proposition) =>
        Seq(Neg, Sp, proposition);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);
}
