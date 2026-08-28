using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DecisionValue;

internal sealed class FreeInformationValueDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A free ignorable observation cannot lower optimal expected value.",
        H("Nonnegative Value of Free Information"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("free-ignorable-information-has-nonnegative-value"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DecisionValue/FreeInformationValue."
                        + "free_ignorable_information_value_nonnegative"),
                H("Free ignorable information has nonnegative value"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The uninformed value is the greatest expected utility obtained by choosing "
                            + "one available action. The informed value is the greatest net expected "
                            + "utility of an admissible observation-dependent policy.")),
                    Paragraph(Text(
                        "The four safeguards are public. Information has zero cost, observation "
                            + "leaves the state unchanged, every constant policy is a permitted way "
                            + "to ignore the observation, and every previously available action "
                            + "remains available after each observation.")),
                    Paragraph(Text(
                        "Choose an action attaining the uninformed optimum. Its constant policy is "
                            + "both permitted and pointwise available by the last two safeguards. "
                            + "The first two safeguards make its informed net value equal to the "
                            + "uninformed optimum, so informed optimality gives the inequality.")),
                    Paragraph(Text(
                        "The expectation functional, observation, world transition, utility, costs, "
                            + "action sets, and policy set are independent source inputs. Repository "
                            + "and pinned-library searches found no exact theorem combining them."))),
                DescribeRole.Theorem))));

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

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula evidence = F.Id("E");
        Formula action = F.Id("U");
        Formula expectation = Seq(Mathbb, Grp(F.Id("E")));
        Formula observe = F.Id("observe");
        Formula transition = F.Id("worldAfterObservation");
        Formula utility = F.Id("V");
        Formula cost = F.Id("informationCost");
        Formula actionsBefore = F.Id("A0");
        Formula actionsAfter = F.Id("A1");
        Formula policies = F.Id("P");
        Formula uninformed = Subscript(F.Id("W"), D(0));
        Formula informed = Subscript(F.Id("W"), evidence);
        Formula selectedAction = F.Id("u");
        Formula observedValue = F.Id("e");
        Formula currentState = F.Id("x");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula policyType = Arrow(evidence, action);
        Formula actionSet = Call("Set", action);
        Formula policySet = Call("Set", policyType);
        Formula constantPolicy = Seq(Open, observedValue, Colon, Sp, evidence, Close,
            Sp, Mapsto, Sp, selectedAction);
        Formula uninformedImage = Call("image",
            Call("uninformedExpectedValue", expectation, utility), actionsBefore);
        Formula informedImage = Call("image",
            Call("informedExpectedValue", expectation, observe, transition, utility, cost),
            Call("admissiblePolicies", policies, actionsAfter));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp,
                Typed(Seq(state, Comma, Sp, evidence, Comma, Sp, action), type), Comma),
            Seq(Grp(), Forall, Sp,
                Typed(expectation, Call("Concept", Arrow(state, real), real)), Comma),
            Seq(Grp(), Forall, Sp,
                Typed(observe, Call("Concept", state, evidence)), Comma, Sp,
                Typed(transition, Arrow(evidence, Arrow(state, state))), Comma),
            Seq(Grp(), Forall, Sp,
                Typed(utility, Call("Concept", state, Arrow(action, real))), Comma, Sp,
                Typed(cost, real), Comma),
            Seq(Grp(), Forall, Sp,
                Typed(actionsBefore, actionSet), Comma, Sp,
                Typed(actionsAfter, Arrow(evidence, actionSet)), Comma),
            Seq(Grp(), Forall, Sp, Typed(policies, policySet), Comma, Sp,
                Typed(Seq(uninformed, Comma, Sp, informed), real), Comma),
            Seq(Grp(), Forall, Sp,
                Typed(F.Id("informationFree"), Seq(cost, Sp, Eq, Sp, D(0))), Comma),
            Seq(Grp(), Forall, Sp,
                Typed(F.Id("observationDoesNotChangeWorld"), Seq(
                    Forall, Sp, Typed(observedValue, evidence), Comma, Sp,
                    Typed(currentState, state), Comma, Sp,
                    Apply(transition, observedValue, currentState), Sp, Eq, Sp, currentState)),
                Comma),
            Seq(Grp(), Forall, Sp,
                Typed(F.Id("canIgnoreInformation"), Seq(
                    Forall, Sp, Typed(selectedAction, action), Comma, Sp,
                    selectedAction, Sp, InMacro, Sp, actionsBefore, Sp, Rightarrow, Sp,
                    constantPolicy, Sp, InMacro, Sp, policies)), Comma),
            Seq(Grp(), Forall, Sp,
                Typed(F.Id("actionSetNotReduced"), Seq(
                    Forall, Sp, Typed(observedValue, evidence), Comma, Sp,
                    actionsBefore, Sp, Subseteq, Sp, Apply(actionsAfter, observedValue))),
                Comma),
            Seq(Grp(), Forall, Sp,
                Typed(F.Id("uninformedOptimal"),
                    Call("IsGreatest", uninformedImage, uninformed)), Comma),
            Seq(Grp(), Forall, Sp,
                Typed(F.Id("informedOptimal"),
                    Call("IsGreatest", informedImage, informed)), Comma),
            Seq(Grp(), uninformed, Sp, Leq, Sp, informed, Dot),
        ]));
    }

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
