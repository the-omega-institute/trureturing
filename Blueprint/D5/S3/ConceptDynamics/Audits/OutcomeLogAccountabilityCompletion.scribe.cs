using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Audits;

internal sealed class OutcomeLogAccountabilityCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Outcome-only logs omit accountability, whose canonical completion is least.",
        H("Outcome Log Accountability Completion"),
        Blocks(Describe.Lean(
            DescribeId.Create("outcome-log-obstruction-and-accountability-completion"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Audits/OutcomeLogAccountabilityCompletion."
                    + "outcome_log_obstruction_and_accountability_completion"),
            H("Outcome-only logs cannot recover full accountability"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Decision, rule, actor, and provenance are independent readouts on the same "
                        + "state carrier. Their nested canonical join is the full accountability "
                        + "readout.")),
                Paragraph(Text(
                    "A log that factors through the decision identifies the displayed witness "
                        + "states. Their different actor or rule coordinate makes the full "
                        + "accountability readout vary on that log fiber, so no recovery factor "
                        + "can exist.")),
                Paragraph(Text(
                    "Joining the log with the accountability readout retains each component. "
                        + "Pairing any two supplied factors proves that this completion is below "
                        + "every common refinement."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Refines(Formula coarse, Formula fine) =>
        Call("Refines", coarse, fine);

    private static Formula Join(Formula first, Formula second) =>
        Call("conceptJoin", first, second);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("Z");
        Formula decisionType = F.Id("Decision");
        Formula ruleType = F.Id("Rule");
        Formula actorType = F.Id("Actor");
        Formula provenanceType = F.Id("Provenance");
        Formula decision = F.Id("D");
        Formula rule = F.Id("R");
        Formula actor = F.Id("A");
        Formula provenance = F.Id("P");
        Formula left = F.Id("z");
        Formula right = F.Id("zp");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula accountability = Join(Join(Join(decision, rule), actor), provenance);
        Formula witness = Seq(
            Apply(decision, left), Sp, Eq, Sp, Apply(decision, right), Sp, Land, Sp,
            Open,
            Apply(actor, left), Sp, Neq, Sp, Apply(actor, right), Sp, Lor, Sp,
            Apply(rule, left), Sp, Neq, Sp, Apply(rule, right),
            Close);

        Formula logType = F.Id("Log");
        Formula log = F.Id("L");
        Formula completed = Join(log, accountability);
        Formula obstruction = Seq(
            Forall, Sp, Typed(logType, type), Comma, Sp,
            Typed(log, Arrow(state, logType)), Comma, RowBreak, Grp(),
            Refines(log, decision), Sp, Rightarrow, Sp,
            Neg, Sp, Refines(accountability, log));

        Formula candidateType = F.Id("Candidate");
        Formula candidate = F.Id("K");
        Formula minimality = Seq(
            Forall, Sp, Typed(candidateType, type), Comma, Sp,
            Typed(candidate, Arrow(state, candidateType)), Comma, RowBreak, Grp(),
            Open,
            Refines(log, candidate), Sp, Land, Sp,
            Refines(accountability, candidate),
            Close, Sp, Rightarrow, Sp, Refines(completed, candidate));
        Formula completion = Seq(
            Forall, Sp, Typed(logType, type), Comma, Sp,
            Typed(log, Arrow(state, logType)), Comma, RowBreak, Grp(),
            Refines(log, completed), Sp, Land, RowBreak, Grp(),
            Refines(accountability, completed), Sp, Land, RowBreak, Grp(),
            minimality);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(
                Seq(
                    state, Comma, Sp, decisionType, Comma, Sp, ruleType, Comma, Sp,
                    actorType, Comma, Sp, provenanceType),
                type),
            Comma, RowBreak, Grp(),
            Typed(decision, Arrow(state, decisionType)), Comma, Sp,
            Typed(rule, Arrow(state, ruleType)), Comma, RowBreak, Grp(),
            Typed(actor, Arrow(state, actorType)), Comma, Sp,
            Typed(provenance, Arrow(state, provenanceType)), Comma, RowBreak, Grp(),
            Typed(Seq(left, Comma, Sp, right), state), Comma, RowBreak, Grp(),
            witness, Sp, Rightarrow, RowBreak, Grp(),
            Open, obstruction, Close, Sp, Land, RowBreak, Grp(),
            completion, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
