using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Reversibility;

internal sealed class WorldChangeValueReversalDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Reversibility/WorldChangeValueReversal."
            + "world_change_can_reverse_waiting_value";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A changed world can make waiting strictly worse despite preserving every action.",
        H("World Change Can Reverse Waiting Value"),
        Blocks(Describe.Lean(
            DescribeId.Create("world-change-can-reverse-waiting-value"),
            DeclarationHandle.Create(Declaration),
            H("World change can reverse waiting value"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The witness has two world states, one observation, and one action. "
                        + "Waiting changes the initially evaluated state, while information "
                        + "has zero cost and the action set is preserved exactly.")),
                Paragraph(Text(
                    "Every constant policy is available. The same transition that witnesses "
                        + "world change is used by the informed-value functional, so the positive "
                        + "safeguards and strict reversal are not separable constructions.")),
                Paragraph(Text(
                    "Immediate action has value one at the initial state. After waiting, the "
                        + "world transition reaches the zero-utility state, so every admissible "
                        + "policy has value zero and waiting is strictly worse.")),
                Paragraph(Text(
                    "The theorem reuses the canonical decision-value primitives. The adjacent "
                        + "opportunity-loss theorem changes the action set instead of the world, "
                        + "and repository and pinned-library searches found no exact theorem for "
                        + "this countermodel."))),
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
            "Concept", Arrow(boolean, real), real);
        Formula observeType = Call("Concept", boolean, unit);
        Formula worldType = Arrow(unit, Arrow(boolean, boolean));
        Formula utilityType = Call("Concept", boolean, Arrow(unit, real));
        Formula beforeType = Call("Set", unit);
        Formula afterType = Arrow(unit, Call("Set", unit));
        Formula candidatesType = Call("Set", Arrow(unit, unit));
        Formula changedWorld = Seq(
            Open,
            Exists, Sp, Typed(evidence, unit), Comma, Sp,
            Typed(state, boolean), Comma, Sp,
            Apply(Apply(world, evidence), state), Sp, Neq, Sp, state,
            Close);
        Formula constantPolicies = Seq(
            Open,
            Forall, Sp, Typed(action, unit), Comma, Sp,
            action, Sp, InMacro, Sp, before, Sp, Rightarrow, Sp,
            Call("const", action), Sp, InMacro, Sp, candidates,
            Close);
        Formula actionsPreserved = Seq(
            Open,
            Forall, Sp, Typed(evidence, unit), Comma, Sp,
            before, Sp, Subseteq, Sp, Apply(after, evidence),
            Close);
        Formula uninformedValues = Seq(
            OpenBrace,
            Call("uninformedExpectedValue", expectation, utility, action),
            Sp, Mid, Sp, action, Sp, InMacro, Sp, before,
            CloseBrace);
        Formula admissible = Call("admissiblePolicies", candidates, after);
        Formula informedValues = Seq(
            OpenBrace,
            Call(
                "informedExpectedValue",
                expectation,
                observe,
                world,
                utility,
                zero,
                policy),
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
            changedWorld, Sp, Land, RowBreak, Grp(),
            constantPolicies, Sp, Land, RowBreak, Grp(),
            actionsPreserved, Sp, Land, RowBreak, Grp(),
            Call("IsGreatest", uninformedValues, uninformed), Sp, Land, RowBreak, Grp(),
            Call("IsGreatest", informedValues, informed), Sp, Land, RowBreak, Grp(),
            informed, Sp, Lt, Sp, uninformed, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
