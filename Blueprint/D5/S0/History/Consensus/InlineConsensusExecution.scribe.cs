using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Consensus;

internal sealed class InlineConsensusExecutionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Executions preserve retry uniqueness and consume finite protocol resources.",
        H("Inline Consensus Execution"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a-fix-invalidates-any-stale-termination-permit"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusExecution."
                    + "no_stale_termination_permit_after_fix"),
                H("A fix invalidates any stale termination permit"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("config"), Comma, Sp, F.Id("start"), Comma, Sp,
                    F.Id("repaired"), Comma, Esc,
                    Call("ProtocolStep", F.Id("config"), F.Id("start"),
                        Call("boundedPass", Field("start", "stage"), F.Id("fixPass")),
                        F.Id("repaired")),
                    Sp, Rightarrow, Sp,
                    Field("repaired", "terminationExit"), Sp, Eq, Sp, F.Id("none"),
                    Sp, Land, Sp,
                    Field("repaired", "terminationEpoch"), Sp, Eq, Sp, F.Id("none"),
                    RowBreak, Sp, Land, Sp,
                    Forall, Sp, F.Id("final"), Comma, Esc, Neg,
                    Call("ProtocolStep", F.Id("config"), F.Id("repaired"),
                        F.Id("finish"), F.Id("final"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every bounded fix pass, the repaired state has neither a recorded "
                        + "termination exit nor a termination epoch, and no finish transition can "
                        + "start from that repaired state. The theorem concerns only the state "
                        + "produced by the given fix transition; it does not assert that every later "
                        + "state is unable to finish."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("termination-evaluation-requires-a-current-done-review"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusExecution."
                    + "termination_gate_requires_current_done_review"),
                H("Termination evaluation requires a current done review"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("config"), Comma, Sp, F.Id("state"), Comma, Sp,
                    F.Id("final"), Comma, Esc,
                    Call("ProtocolStep", F.Id("config"), F.Id("state"),
                        Call("boundedPass", Field("state", "stage"),
                            F.Id("terminationGate")),
                        F.Id("final")),
                    Sp, Rightarrow, Sp,
                    Field("state", "reviewExit"), Sp, Eq, Sp,
                    Call("some", F.Id("done")), Sp, Land, Sp,
                    Field("state", "reviewEpoch"), Sp, Eq, Sp,
                    Call("some", Field("state", "artifactEpoch"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A termination-gate transition can be taken only when its source state "
                        + "records a done review whose epoch equals that state's artifact epoch. "
                        + "The conclusion constrains the source state; it does not by itself state "
                        + "which termination exit the resulting state records."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-termination-router-is-sound-maximal-and-unique"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusExecution."
                    + "termination_router_sound_maximal_unique"),
                H("The termination router is sound, maximal, and unique"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("Sound", F.Id("optimalTerminationRule")),
                    RowBreak, Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("rule"), Comma, Esc,
                    Call("Sound", F.Id("rule")), Sp, Rightarrow, Sp,
                    Call("RuleLE", F.Id("rule"), F.Id("optimalTerminationRule")), Close,
                    RowBreak, Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("rule"), Comma, Esc,
                    Call("Greatest", F.Id("rule")), Sp, Rightarrow, Sp,
                    F.Id("rule"), Sp, Eq, Sp, F.Id("optimalTerminationRule"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Soundness means that every admitted observation is free of the Lean "
                        + "TerminationHazard. The second conjunct says every sound rule is pointwise "
                        + "below optimalTerminationRule. The third says any Greatest sound rule "
                        + "equals optimalTerminationRule; it does not assert uniqueness for a weaker "
                        + "or differently defined ordering.")),
                    Paragraph(Text(
                        "The proof identifies permit observations with an exact roster whose three "
                        + "named results are all satisfied, then uses Mathlib's IsGreatest.unique for "
                        + "the final equality. The proposition is internal to the Lean model and makes "
                        + "no claim about a current or future external plugin version."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("maximal-runs-preserve-budgets-and-have-an-explicit-length-bound"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusExecution."
                    + "every_maximal_run_is_bounded"),
                H("Maximal runs preserve budgets and have an explicit length bound"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("config"), Comma, Sp, F.Id("run"), Colon, Sp,
                    Call("MaximalRun", F.Id("inlineConsensusModel"), F.Id("config")),
                    Comma, Esc,
                    Call("WithinRetryBudgets", F.Id("config"), Field("run", "events")),
                    RowBreak, Sp, Land, Sp,
                    Call("NoCarrierReopened", Field("run", "events")),
                    RowBreak, Sp, Land, Sp,
                    Call("sharedPassCount", Field("run", "events")), Sp, Le, Sp,
                    Field("config", "sharedPassBudget"),
                    RowBreak, Sp, Land, Sp,
                    Call("length", Field("run", "events")), Sp, Le, Sp,
                    Call("explicitRunBound", F.Id("config"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every MaximalRun of inlineConsensusModel, each flight-failure event "
                        + "has a positive attempt number within its configured retry budget, the "
                        + "list of attempted stage-role-carrier keys has no duplicates, the number "
                        + "of bounded-pass events does not exceed the shared-pass budget, and the "
                        + "event-list length does not exceed explicitRunBound config.")),
                    Paragraph(Text(
                        "The explicit bound is the cardinality of FlightKey plus seven stage/live "
                        + "credits plus the configured shared-pass budget. The proof derives all "
                        + "four conjuncts from the guarded execution. It makes no terminal-reachability "
                        + "claim: MaximalRun supplies maximality, but the stated conclusion is exactly "
                        + "the retry, uniqueness, shared-pass, and length conjunction above."))),
                DescribeRole.Theorem))));

    private static Formula Field(string subject, string field) =>
        Seq(F.Id(subject), Dot, F.Id(field));
}
