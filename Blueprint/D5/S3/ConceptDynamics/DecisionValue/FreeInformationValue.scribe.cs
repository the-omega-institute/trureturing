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

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula evidence = F.Id("E");
        Formula action = F.Id("U");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula observe = F.Id("observe");
        Formula worldAfterObservation = F.Id("worldAfterObservation");
        Formula informationCost = F.Id("informationCost");
        Formula actionsBeforeSet = F.Id("A0");
        Formula actionsAfterSet = F.Id("A1");
        Formula candidatePoliciesSet = F.Id("P");
        Formula expectation = Seq(Mathbb, Grp(F.Id("E")));
        Formula utility = F.Id("V");
        Formula transition = F.Id("T");
        Formula cost = Subscript(F.Id("c"), evidence);
        Formula actionsBefore = Subscript(action, D(0));
        Formula actionsAfter = Subscript(action, evidence);
        Formula policies = Pi;
        Formula admissiblePolicies = Subscript(policies, F.Id("adm"));
        Formula uninformed = Subscript(F.Id("W"), D(0));
        Formula informed = Subscript(F.Id("W"), evidence);
        Formula selectedAction = F.Id("u");
        Formula observedPolicy = F.Id("p");
        Formula currentState = F.Id("x");
        Formula observedValue = F.Id("e");
        Formula constantPolicy = Seq(
            Operatorname, Grp(F.Id("const")), Open, selectedAction, Close);
        Formula beforeMaximum = Seq(
            Max, Underscore, Grp(selectedAction, Sp, InMacro, Sp, actionsBefore),
            Sp, Apply(expectation, Apply(Apply(utility, state), selectedAction)));
        Formula afterMaximum = Seq(
            Max, Underscore, Grp(observedPolicy, Sp, InMacro, Sp,
              admissiblePolicies), Sp,
            Open, Apply(expectation,
              Apply(Apply(utility,
                Apply(Apply(transition, evidence), state)),
                Apply(observedPolicy, evidence))),
            Sp, Minus, Sp, cost, Close);
        Formula admissiblePolicyDefinition = Seq(
            admissiblePolicies, Sp, Eq, Sp, OpenBrace,
            observedPolicy, Sp, InMacro, Sp, policies, Sp, Mid, Sp,
            Forall, Sp, observedValue, Comma, Sp,
            Apply(observedPolicy, observedValue), Sp, InMacro, Sp,
            Subscript(action, observedValue), CloseBrace);
        Formula safeguards = Seq(
            cost, Sp, Eq, Sp, D(0), Comma, Sp,
            Forall, Sp, observedValue, Comma, Sp, currentState, Comma, Sp,
            Apply(Apply(worldAfterObservation, observedValue), currentState), Sp, Eq, Sp,
            currentState, Comma, RowBreak, Grp(),
            Forall, Sp, selectedAction, Sp, InMacro, Sp, actionsBefore, Comma, Sp,
            constantPolicy, Sp, InMacro, Sp, policies, Comma, RowBreak, Grp(),
            Forall, Sp, observedValue, Comma, Sp, actionsBefore, Sp,
            Subseteq, Sp, Subscript(action, observedValue));

        Formula uninformedGreatest = Call(
            "IsGreatest", Call("Image", expectation, utility, actionsBeforeSet), uninformed);
        Formula informedGreatest = Call(
            "IsGreatest", Call("Image", expectation, utility, admissiblePolicies), informed);

        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, evidence, Comma, Sp, action, Colon, Sp, type,
            Comma, RowBreak, Grp(),
            expectation, Colon, Sp,
            Call("Concept", new Formula.TypeArrow(state, real), real), Comma, Sp,
            observe, Colon, Sp, Call("Concept", state, evidence), Comma, Sp,
            worldAfterObservation, Colon, Sp,
            new Formula.TypeArrow(evidence, new Formula.TypeArrow(state, state)), Comma, Sp,
            utility, Colon, Sp,
            Call("Concept", state, new Formula.TypeArrow(action, real)), Comma, Sp,
            informationCost, Colon, Sp, real, Comma, Sp,
            actionsBeforeSet, Colon, Sp, Call("Set", action), Comma, Sp,
            actionsAfterSet, Colon, Sp, new Formula.TypeArrow(evidence, Call("Set", action)),
            Comma, Sp, candidatePoliciesSet, Colon, Sp,
            Call("Set", new Formula.TypeArrow(evidence, action)), Comma, Sp,
            uninformed, Comma, Sp, informed, Colon, Sp, real, Comma, RowBreak, Grp(),
            admissiblePolicyDefinition, Comma, RowBreak, Grp(),
            uninformed, Sp, Eq, Sp, beforeMaximum, Comma, RowBreak, Grp(),
            informed, Sp, Eq, Sp, afterMaximum, Comma, RowBreak, Grp(),
            uninformedGreatest, Comma, Sp, informedGreatest, Comma, RowBreak, Grp(),
            safeguards, RowBreak, Grp(),
            Rightarrow, Sp, informed, Sp, Geq, Sp, uninformed, Dot));
    }

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
