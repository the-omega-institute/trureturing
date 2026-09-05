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
        "All three actor-relative rule forms descend on the full action-input carrier.",
        H("Three Rule Forms and Actor Readout"),
        Blocks(Describe.Lean(
            DescribeId.Create("three-rule-actor-decidability"),
            DeclarationHandle.Create(Declaration),
            H("Compatibility, separation, and recipient descent"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The actor-visible input retains the action and recipient coordinates "
                        + "while replacing the state by the actor's readout.")),
                Paragraph(Text(
                    "The frozen observer-action criterion supplies compatibility, universal "
                        + "preservation, and the positive desire-and-ability rule on this "
                        + "carrier. Its contrapositive yields the separating desire.")),
                Paragraph(Text(
                    "For the actual transition evaluated by the recipient's desire, Mathlib's "
                        + "factorization criterion exposes the descended predicate explicitly.")),
                Paragraph(Text(
                    "Repository search found the frozen full-carrier owner but no declaration "
                        + "that publicly states both the separating witness and descended "
                        + "predicate. Pinned Mathlib supplies the latter factorization step."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula prop = Seq(Operatorname, Grp(F.Id("Prop")));
        Formula stateType = F.Id("X");
        Formula actionType = F.Id("U");
        Formula agentType = F.Id("I");
        Formula observation = F.Id("B");
        Formula readout = F.Id("readout");
        Formula transition = F.Id("transition");
        Formula actor = F.Id("actor");
        Formula agent = F.Id("agent");
        Formula input = F.Id("input");
        Formula wish = F.Id("wish");
        Formula capable = F.Id("capable");
        Formula otherWish = F.Id("otherWish");
        Formula recipient = F.Id("recipient");
        Formula descended = F.Id("descended");
        Formula actorInputReadout = F.Id("actorInputReadout");
        Formula mirroredTransition = F.Id("mirroredTransition");
        Formula actualTransition = F.Id("actualTransition");
        Formula compatible = F.Id("compatible");
        Formula inputType = Product(stateType, actionType, agentType);
        Formula visibleInputType = Product(
            Apply(observation, actor), actionType, agentType);
        Formula statePredicate = Arrow(stateType, prop);
        Formula inputPredicate = Arrow(inputType, prop);

        Formula readableWish = Factor(wish, Apply(readout, actor));
        Formula readableCapability = Factor(capable, actorInputReadout);
        Formula negativeMirroredWish = Lambda(
            Typed(input, inputType),
            Negate(Apply(wish, Apply(mirroredTransition, input))));
        Formula positiveMirroredRule = Lambda(
            Typed(input, inputType),
            Seq(
                Apply(wish, Apply(mirroredTransition, input)),
                Sp, Land, Sp,
                Apply(capable, input)));
        Formula positiveActualWish = Lambda(
            Typed(input, inputType),
            Apply(
                otherWish,
                Call("recipient", input),
                Apply(actualTransition, input)));
        Formula negativeActualWish = Lambda(
            Typed(input, inputType),
            Negate(Apply(
                otherWish,
                Call("recipient", input),
                Apply(actualTransition, input))));

        Formula preservation = Seq(
            readableWish, Sp, Rightarrow, Sp,
            compatible, Sp, Rightarrow, Sp,
            Factor(negativeMirroredWish, actorInputReadout));
        Formula forwardClause = Bind(
            FormulaQuantifier.ForAll, "wish", statePredicate, preservation);
        Formula separatingClause = Seq(
            Negate(compatible), Sp, Rightarrow, Sp,
            Bind(
                FormulaQuantifier.Exists,
                "wish",
                statePredicate,
                Seq(
                    readableWish, Sp, Land, Sp,
                    Negate(Factor(negativeMirroredWish, actorInputReadout)))));
        Formula universalPreservation = Bind(
            FormulaQuantifier.ForAll,
            "wish",
            statePredicate,
            Seq(
                readableWish, Sp, Rightarrow, Sp,
                Factor(negativeMirroredWish, actorInputReadout)));
        Formula criterionClause = Seq(
            compatible, Sp, Leftrightarrow, Sp,
            Open, universalPreservation, Close);
        Formula positiveClause = BindMany(
            FormulaQuantifier.ForAll,
            [("wish", statePredicate), ("capable", inputPredicate)],
            Seq(
                readableWish, Sp, Rightarrow, Sp,
                readableCapability, Sp, Rightarrow, Sp,
                compatible, Sp, Rightarrow, Sp,
                Factor(positiveMirroredRule, actorInputReadout)));
        Formula otherWishType = Seq(
            Forall, Sp, Typed(recipient, agentType), Comma, Sp,
            Arrow(stateType, prop));
        Formula descendedPredicate = Seq(
            positiveActualWish, Sp, Eq, Sp,
            Call("compose", descended, actorInputReadout));
        Formula structuralClause = Bind(
            FormulaQuantifier.ForAll,
            "otherWish",
            otherWishType,
            Seq(
                Factor(negativeActualWish, actorInputReadout),
                Sp, Leftrightarrow, Sp,
                Bind(
                    FormulaQuantifier.Exists,
                    "descended",
                    Arrow(visibleInputType, prop),
                    descendedPredicate)));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp,
                Typed(
                    Seq(stateType, Comma, Sp, actionType, Comma, Sp, agentType),
                    type),
                Comma),
            Seq(Typed(observation, Arrow(agentType, type)), Comma),
            Seq(
                Typed(
                    readout,
                    Seq(
                        Open, Typed(agent, agentType), Close,
                        Sp, To, Sp,
                        Arrow(stateType, Apply(observation, agent)))),
                Comma),
            Seq(
                Typed(
                    transition,
                    Arrow(
                        stateType,
                        Arrow(actionType, Arrow(agentType, Arrow(agentType, stateType))))),
                Comma),
            Seq(Typed(actor, agentType), Comma),
            Seq(
                Operatorname, Grp(F.Id("let")), Sp,
                actorInputReadout, Colon, Sp,
                Arrow(inputType, visibleInputType),
                Sp, Colon, Eq, Sp,
                Lambda(
                    Typed(input, inputType),
                    Call(
                        "triple",
                        Apply(Apply(readout, actor), Call("state", input)),
                        Call("action", input),
                        Call("recipient", input))),
                Comma),
            Seq(
                mirroredTransition, Colon, Sp, Arrow(inputType, stateType),
                Sp, Colon, Eq, Sp,
                Lambda(
                    Typed(input, inputType),
                    Apply(
                        transition,
                        Call("state", input),
                        Call("action", input),
                        Call("recipient", input),
                        actor)),
                Comma),
            Seq(
                actualTransition, Colon, Sp, Arrow(inputType, stateType),
                Sp, Colon, Eq, Sp,
                Lambda(
                    Typed(input, inputType),
                    Apply(
                        transition,
                        Call("state", input),
                        Call("action", input),
                        actor,
                        Call("recipient", input))),
                Comma),
            Seq(
                compatible, Colon, Sp, prop, Sp, Colon, Eq, Sp,
                Factor(
                    Call("compose", Apply(readout, actor), mirroredTransition),
                    actorInputReadout),
                Sp, Operatorname, Grp(F.Id("in"))),
            Seq(Open, forwardClause, Close, Sp, Land),
            Seq(Open, separatingClause, Close, Sp, Land),
            Seq(Open, criterionClause, Close, Sp, Land),
            Seq(Open, positiveClause, Close, Sp, Land),
            Seq(Open, structuralClause, Close, Dot),
        ]));
    }

    private static Formula Bind(
        FormulaQuantifier quantifier,
        string variable,
        Formula type,
        Formula body) =>
        new Formula.BindMany(
            quantifier,
            [new Formula.BoundVariable(
                FormulaIdentifier.Create(variable), type)],
            body);

    private static Formula BindMany(
        FormulaQuantifier quantifier,
        (string Variable, Formula Type)[] binders,
        Formula body) =>
        new Formula.BindMany(
            quantifier,
            [.. binders.Select(binder => new Formula.BoundVariable(
                FormulaIdentifier.Create(binder.Variable),
                binder.Type))],
            body);

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

    private static Formula Product(params Formula[] factors)
    {
        var items = new List<Formula>();
        for (var index = 0; index < factors.Length; index++)
        {
            if (index > 0) items.AddRange([Sp, Times, Sp]);
            items.Add(factors[index]);
        }

        return Seq([.. items]);
    }
}
