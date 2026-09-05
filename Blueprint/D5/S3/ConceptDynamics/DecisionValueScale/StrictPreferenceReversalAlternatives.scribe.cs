using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DecisionValueScale;

internal sealed class StrictPreferenceReversalAlternativesDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DecisionValueScale/StrictPreferenceReversalAlternatives."
            + "strict_preference_reversal_forces_state_change_or_behavioral_unfaithfulness";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A strict preference reversal forces a change in a determining state or a "
            + "loss of behavioral fidelity.",
        H("Strict Preference Reversal Alternatives"),
        Blocks(Describe.Lean(
            DescribeId.Create("strict-preference-reversal-alternatives"),
            DeclarationHandle.Create(Declaration),
            H("A strict reversal excludes one invariant scalar representation"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Both observations use the same option carrier, the same two options, "
                        + "and the same fact. Their behavior relations rank the options in "
                        + "opposite directions.")),
                Paragraph(Text(
                    "No single real-valued function can respect both strict rankings. "
                        + "For a shared utility rule indexed by value, self, temporal, and "
                        + "context states, the reversal therefore forces one state to change "
                        + "or at least one behavior relation not to respect the induced "
                        + "strict ranking.")),
                Paragraph(Text(
                    "The proof applies the frozen strict-order reversal theorem both to the "
                        + "putative common scalar function and to the state-indexed utility "
                        + "after all four state coordinates are assumed unchanged."))),
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
        new Formula.TypeArrow(domain, codomain);

    private static Formula Represents(
        Formula behavior,
        Formula value,
        Formula choice)
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        return Seq(
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, choice, Comma, Sp,
            Apply(behavior, x, y), Sp, Rightarrow, Sp,
            Apply(value, x), Sp, Gt, Sp, Apply(value, y));
    }

    private static Formula StateRepresents(
        Formula behavior,
        Formula utility,
        Formula valueState,
        Formula selfConcept,
        Formula timePreference,
        Formula context,
        Formula facts,
        Formula choice)
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula contextAtFacts = Apply(context, facts);
        return Seq(
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, choice, Comma, Sp,
            Apply(behavior, x, y), Sp, Rightarrow, Sp,
            Apply(utility, valueState, selfConcept, timePreference,
                contextAtFacts, x),
            Sp, Gt, Sp,
            Apply(utility, valueState, selfConcept, timePreference,
                contextAtFacts, y));
    }

    private static Formula TheoremFormula()
    {
        Formula choice = F.Id("U");
        Formula fact = F.Id("F");
        Formula valueStateType = F.Id("V");
        Formula selfConceptType = F.Id("S");
        Formula timePreferenceType = F.Id("T");
        Formula contextConceptType = F.Id("C");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula proposition = Seq(Operatorname, Grp(F.Id("Prop")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));

        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula facts = F.Id("f");
        Formula valueAtFirst = new Formula.Subscript(F.Id("v"), D(0));
        Formula valueAtSecond = new Formula.Subscript(F.Id("v"), D(1));
        Formula selfAtFirst = new Formula.Subscript(F.Id("s"), D(0));
        Formula selfAtSecond = new Formula.Subscript(F.Id("s"), D(1));
        Formula timeAtFirst = new Formula.Subscript(F.Id("t"), D(0));
        Formula timeAtSecond = new Formula.Subscript(F.Id("t"), D(1));
        Formula contextAtFirst = new Formula.Subscript(F.Id("c"), D(0));
        Formula contextAtSecond = new Formula.Subscript(F.Id("c"), D(1));
        Formula behaviorAtFirst = new Formula.Subscript(F.Id("B"), D(0));
        Formula behaviorAtSecond = new Formula.Subscript(F.Id("B"), D(1));
        Formula utility = F.Id("u");
        Formula commonValue = F.Id("w");

        Formula contextType = Arrow(fact, contextConceptType);
        Formula behaviorType = Arrow(choice, Arrow(choice, proposition));
        Formula utilityType = Arrow(valueStateType,
            Arrow(selfConceptType,
                Arrow(timePreferenceType,
                    Arrow(contextConceptType, Arrow(choice, real)))));
        Formula commonValueType = Arrow(choice, real);

        Formula reversal = Seq(
            Apply(behaviorAtFirst, a, b), Sp, Land, Sp,
            Apply(behaviorAtSecond, b, a));
        Formula noCommonValue = Seq(
            Neg, Sp, Exists, Sp, commonValue, Colon, Sp, commonValueType,
            Comma, Sp, Open,
            Open,
            Represents(behaviorAtFirst, commonValue, choice),
            Close, Sp, Land, Sp, Open,
            Represents(behaviorAtSecond, commonValue, choice),
            Close, Close);
        Formula firstFaithful = StateRepresents(
            behaviorAtFirst, utility, valueAtFirst, selfAtFirst, timeAtFirst,
            contextAtFirst, facts, choice);
        Formula secondFaithful = StateRepresents(
            behaviorAtSecond, utility, valueAtSecond, selfAtSecond, timeAtSecond,
            contextAtSecond, facts, choice);
        Formula alternatives = Seq(
            valueAtFirst, Sp, Neq, Sp, valueAtSecond, Sp, Lor, Sp,
            selfAtFirst, Sp, Neq, Sp, selfAtSecond, Sp, Lor, Sp,
            timeAtFirst, Sp, Neq, Sp, timeAtSecond, Sp, Lor, Sp,
            contextAtFirst, Sp, Neq, Sp, contextAtSecond, Sp, Lor, Sp,
            Neg, Sp, Open,
            Open, firstFaithful, Close, Sp, Land, Sp,
            Open, secondFaithful, Close,
            Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            choice, Comma, Sp, fact, Comma, Sp, valueStateType, Comma, Sp,
            selfConceptType, Comma, Sp, timePreferenceType, Comma, Sp,
            contextConceptType, Colon, Sp, type, Comma, RowBreak, Grp(),
            a, Comma, Sp, b, Colon, Sp, choice, Comma, Sp,
            facts, Colon, Sp, fact, Comma, RowBreak, Grp(),
            valueAtFirst, Comma, Sp, valueAtSecond, Colon, Sp,
            valueStateType, Comma, Sp,
            selfAtFirst, Comma, Sp, selfAtSecond, Colon, Sp,
            selfConceptType, Comma, RowBreak, Grp(),
            timeAtFirst, Comma, Sp, timeAtSecond, Colon, Sp,
            timePreferenceType, Comma, Sp,
            contextAtFirst, Comma, Sp, contextAtSecond, Colon, Sp,
            contextType, Comma, RowBreak, Grp(),
            behaviorAtFirst, Comma, Sp, behaviorAtSecond, Colon, Sp,
            behaviorType, Comma, Sp,
            utility, Colon, Sp, utilityType, Comma, RowBreak, Grp(),
            Open, reversal, Close, Sp, Rightarrow, RowBreak, Grp(),
            Open, noCommonValue, Close, Sp, Land, RowBreak, Grp(),
            Open, alternatives, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
