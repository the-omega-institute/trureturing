using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Reversibility;

internal sealed class WaitingCostValueReversalDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Reversibility/WaitingCostValueReversal."
            + "positive_waiting_cost_can_reverse_value";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive waiting cost alone can make delayed optimal value strictly lower.",
        H("Waiting Cost Can Reverse Value"),
        Blocks(Describe.Lean(
            DescribeId.Create("positive-waiting-cost-can-reverse-value"),
            DeclarationHandle.Create(Declaration),
            H("Positive waiting cost can reverse optimal value"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The witness has one state, one observation, and one action. Observation "
                        + "leaves the world unchanged, the action set is exactly preserved, "
                        + "and the constant policy remains admissible.")),
                Paragraph(Text(
                    "Immediate action has value one. Delayed action has the same gross utility "
                        + "and a positive cost of one, so its net value is zero.")),
                Paragraph(Text(
                    "Both optimality claims and the strict comparison use this same decision "
                        + "model; positive cost is the only failed safeguard."))),
            DescribeRole.Theorem))));

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula unit = F.Id("Unit");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula expectation = Seq(Mathbb, Grp(F.Id("E")));
        Formula observe = F.Id("q");
        Formula world = F.Id("T");
        Formula utility = F.Id("V");
        Formula before = F.Id("A");
        Formula after = F.Id("B");
        Formula candidates = Pi;
        Formula cost = F.Id("c");
        Formula uninformed = F.Id("W");
        Formula informed = F.Id("Z");
        Formula evidence = F.Id("e");
        Formula state = F.Id("x");
        Formula action = F.Id("u");
        Formula policy = F.Id("p");
        Formula expectationType = Call("Concept", Arrow(unit, real), real);
        Formula observeType = Call("Concept", unit, unit);
        Formula worldType = Arrow(unit, Arrow(unit, unit));
        Formula utilityType = Call("Concept", unit, Arrow(unit, real));
        Formula beforeType = Call("Set", unit);
        Formula afterType = Arrow(unit, Call("Set", unit));
        Formula candidatesType = Call("Set", Arrow(unit, unit));
        Formula unchangedWorld = Seq(
            Open,
            Forall, Sp, Typed(evidence, unit), Comma, Sp,
            Typed(state, unit), Comma, Sp,
            Apply(Apply(world, evidence), state), Sp, Eq, Sp, state,
            Close);
        Formula constantPolicies = Seq(
            Open,
            Forall, Sp, Typed(action, unit), Comma, Sp,
            action, Sp, InMacro, Sp, before, Sp, Rightarrow, Sp,
            Call("const", action), Sp, InMacro, Sp, candidates,
            Close);
        Formula actionSetsPreserved = Seq(
            Open,
            Forall, Sp, Typed(evidence, unit), Comma, Sp,
            Apply(after, evidence), Sp, Eq, Sp, before,
            Close);
        Formula uninformedValues = Seq(
            OpenBrace,
            Call("uninformedExpectedValue", expectation, utility, action),
            Sp, Mid, Sp, action, Sp, InMacro, Sp, before,
            CloseBrace);
        Formula informedValues = Seq(
            OpenBrace,
            Call(
                "informedExpectedValue",
                expectation,
                observe,
                world,
                utility,
                cost,
                policy),
            Sp, Mid, Sp, policy, Sp, InMacro, Sp,
            Call("admissiblePolicies", candidates, after),
            CloseBrace);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Exists, Sp,
            Typed(expectation, expectationType), Comma, Sp,
            Typed(observe, observeType), Comma, RowBreak, Grp(),
            Typed(world, worldType), Comma, Sp,
            Typed(utility, utilityType), Comma, RowBreak, Grp(),
            Typed(before, beforeType), Comma, Sp,
            Typed(after, afterType), Comma, RowBreak, Grp(),
            Typed(candidates, candidatesType), Comma, RowBreak, Grp(),
            Typed(cost, real), Comma, Sp,
            Typed(Seq(uninformed, Comma, Sp, informed), real), Comma, RowBreak, Grp(),
            D(0), Sp, Lt, Sp, cost, Sp, Land, RowBreak, Grp(),
            unchangedWorld, Sp, Land, RowBreak, Grp(),
            constantPolicies, Sp, Land, RowBreak, Grp(),
            actionSetsPreserved, Sp, Land, RowBreak, Grp(),
            Call("IsGreatest", uninformedValues, uninformed), Sp, Land, RowBreak, Grp(),
            Call("IsGreatest", informedValues, informed), Sp, Land, RowBreak, Grp(),
            informed, Sp, Lt, Sp, uninformed, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
