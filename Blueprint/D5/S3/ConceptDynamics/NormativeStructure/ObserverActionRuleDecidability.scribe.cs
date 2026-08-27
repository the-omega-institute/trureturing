using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.NormativeStructure;

internal sealed class ObserverActionRuleDecidabilityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/NormativeStructure/ObserverActionRuleDecidability."
            + "observer_action_rule_decidability";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actor-relative readability is preserved exactly by compatible transitions.",
        H("Observer-Relative Action Rule Decidability"),
        Blocks(Describe.Lean(
            DescribeId.Create("observer-action-rule-decidability"),
            DeclarationHandle.Create(Declaration),
            H("Readability of the three action-rule forms"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The actor readout, transition, mirrored transition, actual transition, "
                        + "and actor-visible action input are constructed explicitly on the "
                        + "source carrier.")),
                Paragraph(Text(
                    "Transition compatibility is equivalent to readability of every negative "
                        + "mirrored wish. This includes the source converse: an incompatible "
                        + "transition is separated by a readable wish.")),
                Paragraph(Text(
                    "Under the same compatibility, a readable wish conjoined with a readable "
                        + "capability remains readable. For the actual transition evaluated by "
                        + "another recipient's wish, readability of the negated rule is exactly "
                        + "readability of the pulled-back wish itself."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

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

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula LambdaOf(
        Formula variable,
        Formula variableType,
        Formula body) =>
        Seq(Lambda, Sp, Typed(variable, variableType), Comma, Sp, body);

    private static Formula Factors(Formula value, Formula through) =>
        Call("FactorsThrough", value, through);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula prop = F.Id("Prop");
        Formula state = F.Id("X");
        Formula action = F.Id("U");
        Formula role = F.Id("I");
        Formula value = F.Id("B");
        Formula readout = F.Id("q");
        Formula transition = F.Id("F");
        Formula actor = F.Id("i");
        Formula input = F.Id("z");
        Formula wish = F.Id("W");
        Formula capable = F.Id("C");
        Formula otherWish = F.Id("V");
        Formula visibleInput = F.Id("Q");
        Formula mirrored = F.Id("M");
        Formula actual = F.Id("A");
        Formula inputType = Product(state, action, role);
        Formula actorReadout = Apply(readout, actor);
        Formula readableWish = Factors(wish, actorReadout);
        Formula compatible = Factors(Call("compose", actorReadout, mirrored), visibleInput);
        Formula negativeMirrored = LambdaOf(
            input,
            inputType,
            Seq(Neg, Sp, Apply(wish, Apply(mirrored, input))));
        Formula positiveMirrored = LambdaOf(
            input,
            inputType,
            Seq(
                Apply(wish, Apply(mirrored, input)), Sp, Land, Sp,
                Apply(capable, input)));
        Formula negativeActual = LambdaOf(
            input,
            inputType,
            Seq(
                Neg, Sp,
                Apply(
                    otherWish,
                    Call("recipient", input),
                    Apply(actual, input))));
        Formula positiveActual = LambdaOf(
            input,
            inputType,
            Apply(
                otherWish,
                Call("recipient", input),
                Apply(actual, input)));
        Formula firstClause = new Formula.Logic(
            compatible,
            FormulaLogicOperator.Iff,
            new Formula.BindMany(
                FormulaQuantifier.ForAll,
                [new Formula.BoundVariable(
                    FormulaIdentifier.Create("W"),
                    Arrow(state, prop))],
                new Formula.Logic(
                    readableWish,
                    FormulaLogicOperator.Implies,
                    Factors(negativeMirrored, visibleInput))));
        Formula secondClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("W"), Arrow(state, prop)),
                new Formula.BoundVariable(
                    FormulaIdentifier.Create("C"), Arrow(inputType, prop)),
            ],
            new Formula.Logic(
                And(
                    readableWish,
                    And(Factors(capable, visibleInput), compatible)),
                FormulaLogicOperator.Implies,
                Factors(positiveMirrored, visibleInput)));
        Formula otherWishType = Seq(
            Forall, Sp, Typed(F.Id("j"), role), Comma, Sp,
            Arrow(state, prop));
        Formula thirdClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(
                FormulaIdentifier.Create("V"), otherWishType)],
            new Formula.Logic(
                Factors(negativeActual, visibleInput),
                FormulaLogicOperator.Iff,
                Factors(positiveActual, visibleInput)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(state, Comma, Sp, action, Comma, Sp, role), type),
            Comma, RowBreak, Grp(),
            Typed(value, Arrow(role, type)), Comma, Sp,
            Typed(
                readout,
                Seq(
                    Forall, Sp, Typed(F.Id("k"), role), Comma, Sp,
                    Arrow(state, Apply(value, F.Id("k"))))),
            Comma, RowBreak, Grp(),
            Typed(
                transition,
                Arrow(state, Arrow(action, Arrow(role, Arrow(role, state))))),
            Comma, Sp, Typed(actor, role), Comma, RowBreak, Grp(),
            Typed(
                visibleInput,
                Arrow(
                    inputType,
                    Product(Apply(value, actor), action, role))),
            Sp, Colon, Eq, Sp,
            LambdaOf(
                input,
                inputType,
                Call(
                    "triple",
                    Apply(actorReadout, Call("state", input)),
                    Call("action", input),
                    Call("recipient", input))),
            Comma, RowBreak, Grp(),
            Typed(mirrored, Arrow(inputType, state)), Sp, Colon, Eq, Sp,
            LambdaOf(
                input,
                inputType,
                Apply(
                    transition,
                    Call("state", input),
                    Call("action", input),
                    Call("recipient", input),
                    actor)),
            Comma, RowBreak, Grp(),
            Typed(actual, Arrow(inputType, state)), Sp, Colon, Eq, Sp,
            LambdaOf(
                input,
                inputType,
                Apply(
                    transition,
                    Call("state", input),
                    Call("action", input),
                    actor,
                    Call("recipient", input))),
            Comma, RowBreak, Grp(),
            OpenBracket,
            Open, firstClause, Close, Sp, Land, RowBreak, Grp(),
            Open, secondClause, Close, Sp, Land, RowBreak, Grp(),
            Open, thirdClause, Close,
            CloseBracket, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
