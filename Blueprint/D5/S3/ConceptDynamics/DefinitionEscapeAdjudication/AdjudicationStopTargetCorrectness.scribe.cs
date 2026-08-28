using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeAdjudication;

internal sealed class AdjudicationStopTargetCorrectnessDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/"
            + "AdjudicationStopTargetCorrectness."
            + "adjudication_stop_target_correctness";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The adjudication stop target has an exact finite checker and guarded boundary behavior.",
        H("Adjudication Stop Target Correctness"),
        Blocks(Describe.Lean(
            DescribeId.Create("adjudication-stop-target-correctness"),
            DeclarationHandle.Create(Declaration),
            H("The finite stop checker is exact and rejects vacuous boundary cases"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For arbitrary source types and the decidable premises in the Lean "
                        + "declaration, the named target is compared with the independently "
                        + "expanded oriented stop predicate, both at decision-set level and "
                        + "after projection from the canonical prospective commitment.")),
                Paragraph(Text(
                    "The Boolean checker matches on current first and then performs only "
                        + "decidable scans bounded by the sealed feasible Finset. Its success "
                        + "and failure values are both characterized by the named target.")),
                Paragraph(Text(
                    "The final three clauses separately rule out a missing current, an empty "
                        + "feasible set, and a current action outside that feasible set; thus a "
                        + "vacuous universal domain check cannot manufacture a stop."))),
            DescribeRole.Theorem))));

    private static Formula DecisionTarget(
        Formula admissible, Formula scope, Formula orientation, Formula decision) =>
        Call("AdjudicationStopTargetOnDecisionSet", admissible, scope, orientation, decision);

    private static Formula CommitmentTarget(
        Formula admissible, Formula scope, Formula orientation, Formula commitment) =>
        Call("AdjudicationStopTarget", admissible, scope, orientation, commitment);

    private static Formula Equivalent(Formula left, Formula right) =>
        Seq(left, Sp, Iff, Sp, right);

    private static Formula EqualTo(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);

    private static Formula Conjoined(params Formula[] clauses)
    {
        var items = new List<Formula>();
        for (var index = 0; index < clauses.Length; index++)
        {
            if (index > 0)
            {
                items.AddRange([Sp, Land, RowBreak, Grp()]);
            }
            items.Add(clauses[index]);
        }
        return Seq([.. items]);
    }

    private static Formula TheoremFormula()
    {
        Formula admissible = F.Id("AdmTarget");
        Formula scope = F.Id("InScope");
        Formula orientation = F.Id("O");
        Formula decision = F.Id("D");
        Formula commitment = F.Id("K");
        Formula action = F.Id("a");
        Formula trueValue = F.Id("true");
        Formula falseValue = F.Id("false");
        Formula decisionTarget =
            DecisionTarget(admissible, scope, orientation, decision);
        Formula commitmentTarget =
            CommitmentTarget(admissible, scope, orientation, commitment);
        Formula decisionOriented =
            Call("OrientedStopOnDecisionSet", admissible, scope, orientation, decision);
        Formula commitmentOriented =
            Call("OrientedStop", admissible, scope, orientation, commitment);
        Formula checker = Call("stopCheck", admissible, scope, orientation, decision);
        Formula settlement = Call("settleStop", admissible, scope, orientation, commitment);
        Formula current = Call("current", decision);
        Formula feasible = Call("feasible", decision);
        Formula missingCurrent = Seq(
            EqualTo(current, F.Id("none")), Sp, Rightarrow, Sp,
            Neg, Sp, decisionTarget);
        Formula emptyFeasible = Seq(
            EqualTo(feasible, Emptyset), Sp, Rightarrow, Sp,
            Neg, Sp, decisionTarget);
        Formula infeasibleCurrent = Seq(
            Forall, Sp, action, Comma, Sp,
            Open,
            EqualTo(current, Call("some", action)), Sp, Land, Sp,
            Neg, Sp, Open, action, Sp, InMacro, Sp, feasible, Close,
            Close, Sp, Rightarrow, Sp, Neg, Sp, decisionTarget);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Conjoined(
                Seq(Open, Equivalent(decisionTarget, decisionOriented), Close),
                Seq(Open, Equivalent(commitmentTarget, commitmentOriented), Close),
                Seq(Open, Equivalent(EqualTo(checker, trueValue), decisionTarget), Close),
                Seq(Open, Equivalent(EqualTo(settlement, trueValue), commitmentTarget), Close),
                Seq(Open, Equivalent(
                    EqualTo(settlement, falseValue),
                    Seq(Neg, Sp, commitmentTarget)), Close),
                Seq(Open, missingCurrent, Close),
                Seq(Open, emptyFeasible, Close),
                Seq(Open, infeasibleCurrent, Close)),
            Dot,
            End, Grp(F.Id("gathered"))));
    }
}
