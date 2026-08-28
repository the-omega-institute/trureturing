using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting.Safety;

internal sealed class InvariantSafetyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An inductive invariant makes every finitely reachable state safe.",
        H("Invariant Safety"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("inductive-invariants-certify-finite-executions"),
                DeclarationHandle.Create(
                    "D5/S0/Rewriting/Safety/InvariantSafety.invariant_safety"),
                H("Inductive invariants certify finite executions"),
                StatementSource.FromAuthor(InvariantSafetyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let R be a transition relation, I0 the initial set, J an invariant, "
                            + "and S the safe set. The hypotheses expose all three invariant "
                            + "conditions: I0 is contained in J, J is contained in S, and every "
                            + "R-successor of a state in J remains in J.")),
                    Paragraph(Text(
                        "A reflexive-transitive R path represents an arbitrary finite execution. "
                            + "Direct induction with Relation.ReflTransGen.head_induction_on "
                            + "propagates membership in J from the actual initial state to the "
                            + "endpoint, where containment in S gives safety.")),
                    Paragraph(Text(
                        "Repository and pinned-Mathlib searches found no declaration packaging "
                            + "the complete theorem. The pinned induction primitive is applied "
                            + "directly."))),
                DescribeRole.Theorem))));

    private static Formula Member(Formula value, Formula set) =>
        Seq(value, Sp, InMacro, Sp, set);

    private static Formula Apply2(Formula relation, Formula left, Formula right) =>
        Seq(relation, Open, left, Comma, Sp, right, Close);

    private static Formula InvariantSafetyFormula()
    {
        Formula relation = F.Id("R");
        Formula initial = F.Id("I0");
        Formula invariant = F.Id("J");
        Formula safe = F.Id("S");
        Formula x0 = F.Id("x0");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula state = F.Id("X");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula prop = Seq(Operatorname, Grp(F.Id("Prop")));
        Formula stateSet = Seq(Operatorname, Grp(F.Id("Set")), Open, state, Close);
        Formula relationType = new Formula.TypeArrow(
            state, new Formula.TypeArrow(state, prop));

        return Disp(Seq(
            Forall, Sp, state, Colon, Sp, type, Comma, Sp,
            relation, Colon, Sp, relationType, Comma, RowBreak,
            initial, Comma, Sp, invariant, Comma, Sp, safe, Colon, Sp, stateSet,
            Comma, RowBreak,
            initial, Sp, Subseteq, Sp, invariant, Sp, Land, Sp,
            invariant, Sp, Subseteq, Sp, safe, Sp, Land, RowBreak,
            Open, Forall, Sp, x, Comma, Sp, y, Colon, Sp, state, Comma, Sp,
            Member(x, invariant), Sp, Land, Sp, Apply2(relation, x, y), Sp,
            Rightarrow, Sp, Member(y, invariant), Close, RowBreak,
            Rightarrow, Sp, Forall, Sp, x0, Comma, Sp, x, Colon, Sp, state,
            Comma, RowBreak,
            Member(x0, initial), Sp, Land, Sp,
            Operatorname, Grp(F.Id("ReflTransGen")), Open, relation, Close,
            Open, x0, Comma, Sp, x, Close, Sp, Rightarrow, Sp,
            Member(x, safe), Dot));
    }
}
