using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Reversibility;

internal sealed class OpportunityLossValueReversalDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Reversibility/OpportunityLossValueReversal."
            + "opportunity_loss_can_reverse_waiting_value";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Losing an available action while waiting can strictly lower optimal value.",
        H("Opportunity Loss Can Reverse Waiting Value"),
        Blocks(Describe.Lean(
            DescribeId.Create("opportunity-loss-can-reverse-waiting-value"),
            DeclarationHandle.Create(Declaration),
            H("Opportunity loss can reverse waiting value"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The witness uses one state, one observation, and two actions. The world "
                        + "does not change, information has zero cost, and every constant policy "
                        + "is available as a candidate.")),
                Paragraph(Text(
                    "Before waiting both actions are available. After observation only the "
                        + "lower-utility action remains, so the opportunity-loss witness and both "
                        + "optimization claims refer to the same action sets and utility.")),
                Paragraph(Text(
                    "The best immediate action has value one, whereas every admissible waiting "
                        + "policy must select the remaining action and has value zero. Thus the "
                        + "optimal waiting value is strictly lower."))),
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
        Formula boolean = F.Id("Bool");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula expectation = Seq(Mathbb, Grp(F.Id("E")));
        Formula observe = F.Id("q");
        Formula world = F.Id("T");
        Formula utility = F.Id("V");
        Formula before = F.Id("A");
        Formula after = F.Id("B");
        Formula candidates = Pi;
        Formula uninformed = F.Id("W");
        Formula informed = F.Id("Z");
        Formula evidence = F.Id("e");
        Formula state = F.Id("x");
        Formula action = F.Id("u");
        Formula policy = F.Id("p");
        Formula zero = D(0);
        Formula expectationType = Call(
            "Concept", Arrow(unit, real), real);
        Formula observeType = Call("Concept", unit, unit);
        Formula worldType = Arrow(unit, Arrow(unit, unit));
        Formula utilityType = Call("Concept", unit, Arrow(boolean, real));
        Formula beforeType = Call("Set", boolean);
        Formula afterType = Arrow(unit, Call("Set", boolean));
        Formula candidatesType = Call("Set", Arrow(unit, boolean));
        Formula unchangedWorld = Seq(
            Open,
            Forall, Sp, Typed(evidence, unit), Comma, Sp,
            Typed(state, unit), Comma, Sp,
            Apply(Apply(world, evidence), state), Sp, Eq, Sp, state,
            Close);
        Formula constantPolicies = Seq(
            Open,
            Forall, Sp, Typed(action, boolean), Comma, Sp,
            action, Sp, InMacro, Sp, before, Sp, Rightarrow, Sp,
            Call("const", action), Sp, InMacro, Sp, candidates,
            Close);
        Formula opportunityLoss = Seq(
            Open,
            Exists, Sp, Typed(evidence, unit), Comma, Sp,
            Typed(action, boolean), Comma, Sp,
            action, Sp, InMacro, Sp, before, Sp, Land, Sp,
            Neg, Open, action, Sp, InMacro, Sp, Apply(after, evidence), Close,
            Close);
        Formula uninformedValues = Seq(
            OpenBrace,
            Call("uninformedExpectedValue", expectation, utility, action),
            Sp, Mid, Sp, action, Sp, InMacro, Sp, before,
            CloseBrace);
        Formula admissible = Call("admissiblePolicies", candidates, after);
        Formula informedValues = Seq(
            OpenBrace,
            Call("informedExpectedValue", expectation, observe, world, utility, zero, policy),
            Sp, Mid, Sp, policy, Sp, InMacro, Sp, admissible,
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
            Typed(candidates, candidatesType), Comma, Sp,
            Typed(Seq(uninformed, Comma, Sp, informed), real), Comma, RowBreak, Grp(),
            unchangedWorld, Sp, Land, RowBreak, Grp(),
            constantPolicies, Sp, Land, RowBreak, Grp(),
            opportunityLoss, Sp, Land, RowBreak, Grp(),
            Call("IsGreatest", uninformedValues, uninformed), Sp, Land, RowBreak, Grp(),
            Call("IsGreatest", informedValues, informed), Sp, Land, RowBreak, Grp(),
            informed, Sp, Lt, Sp, uninformed, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
