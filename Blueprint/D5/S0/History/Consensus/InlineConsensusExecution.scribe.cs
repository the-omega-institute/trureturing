using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Consensus;

internal sealed class InlineConsensusExecutionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform independence separates a correlated carrier pair from constant pairs; event-fresh permits and recorded worker attempts govern finite executions.",
        H("Inline Consensus Execution"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("constant-conclusion-pairs-are-uniformly-independent"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusExecution."
                    + "constant_conclusions_are_independent"),
                H("Constant conclusion pairs are uniformly independent"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("ConstantConclusionsAreIndependent")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "ConstantConclusionsAreIndependent is the proposition that for every two "
                        + "Boolean values, the two constant conclusion functions satisfy "
                        + "UniformIndependent. The theorem proves that proposition for all four pairs; "
                        + "it does not claim independence for arbitrary conclusion functions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-heterogeneous-correlated-pair-violates-independence"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusExecution."
                    + "heterogeneous_correlated_conclusions_are_not_independent"),
                H("The heterogeneous correlated pair violates independence"),
                StatementSource.FromAuthor(Disp(Seq(
                    Neg, Sp,
                    Call("UniformIndependent",
                        Call("correlatedConclusion", F.Id("codexCli")),
                        Call("correlatedConclusion", F.Id("nyxidOracle")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The theorem refutes UniformIndependent for the concrete codexCli and "
                        + "nyxidOracle correlatedConclusion functions. Each function returns its latent "
                        + "Boolean world, so each true count and the joint true count are one, while the "
                        + "uniform two-world equation would require two to equal one.")),
                    Paragraph(Text(
                        "Thus the differently labelled carrier pair is proved dependent in this model. "
                        + "The preceding theorem supplies the contrasting degenerate case: every pair "
                        + "of constant conclusion functions satisfies the same independence equation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("every-event-clears-a-carried-permit"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusExecution."
                    + "every_protocol_event_clears_carried_permit"),
                H("Every event clears a carried permit"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("model"), Comma, Sp, F.Id("config"), Comma, Sp,
                    F.Id("start"), Comma, Sp, F.Id("final"), Comma, Sp, F.Id("event"), Comma, Esc,
                    Field("start", "terminationExit"), Sp, Eq, Sp,
                    Call("some", F.Id("permitClaim")), Sp, Rightarrow, Sp,
                    Call("ProtocolStep", F.Id("model"), F.Id("config"), F.Id("start"),
                        F.Id("event"), F.Id("final")), Sp, Rightarrow, Sp,
                    Field("final", "terminationExit"), Sp, Neq, Sp,
                    Call("some", F.Id("permitClaim"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any governing model and any ProtocolStep, a permitClaim carried in the "
                        + "source state's terminationExit cannot remain as permitClaim in the final "
                        + "state. The proof unfolds recordEvent, whose carried-permit branch clears both "
                        + "the exit and its permit epoch."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("carried-permit-invalidation-is-recoverable"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusExecution."
                    + "carried_permit_invalidation_is_recoverable"),
                H("Carried-permit invalidation is recoverable"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("model"), Comma, Esc,
                    Call("RecoverablePermitInvalidation", F.Id("model"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "RecoverablePermitInvalidation model quantifies over a carried permit and an "
                        + "invalidating model.transition. Given the stated budget, well-formedness, live "
                        + "and isolation state, current done review, authorized fresh observation, and "
                        + "remaining-pass hypotheses, it concludes that a fresh terminationGate "
                        + "model.transition from the invalidated state has some reevaluated target.")),
                    Paragraph(Text(
                        "The theorem is conditional on every premise in that predicate. It proves "
                        + "reachability of a fresh evaluation, not that the evaluation necessarily "
                        + "returns permitClaim."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a-fix-prevents-the-repaired-state-from-being-finish-ready"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusExecution."
                    + "no_stale_termination_permit_after_fix"),
                H("A fix prevents the repaired state from being finish-ready"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("model"), Comma, Sp, F.Id("config"), Comma, Sp,
                    F.Id("start"), Comma, Sp, F.Id("attempted"), Comma, Sp,
                    F.Id("repaired"), Comma, Esc,
                    Call("ProtocolStep", F.Id("model"), F.Id("config"), F.Id("start"),
                        Call("boundedPass", Field("start", "stage"), F.Id("fixPass"),
                            F.Id("attempted")),
                        F.Id("repaired")),
                    Sp, Rightarrow, Sp, Neg,
                    Call("FinishPrecondition", F.Id("repaired"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every model, configuration, source state, and attempted-flight set, a "
                        + "fix-pass ProtocolStep produces a repaired state that does not satisfy "
                        + "FinishPrecondition. This is the negation of the complete finish-readiness "
                        + "conjunction; it does not assert which individual conjunct fails."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("termination-evaluation-requires-a-current-done-review"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusExecution."
                    + "termination_gate_requires_current_done_review"),
                H("Termination evaluation requires a current done review"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("model"), Comma, Sp, F.Id("config"), Comma, Sp,
                    F.Id("state"), Comma, Sp, F.Id("attempted"), Comma, Sp,
                    F.Id("final"), Comma, Esc,
                    Call("ProtocolStep", F.Id("model"), F.Id("config"), F.Id("state"),
                        Call("boundedPass", Field("state", "stage"),
                            F.Id("terminationGate"), F.Id("attempted")),
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
                H("The termination router is sound, maximal, unique, and strictly bracketed"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("Sound", F.Id("inlineConsensusModel"), F.Id("optimalTerminationRule")),
                    RowBreak, Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("rule"), Comma, Esc,
                    Call("Sound", F.Id("inlineConsensusModel"), F.Id("rule")),
                    Sp, Rightarrow, Sp,
                    Call("RuleLE", F.Id("rule"), F.Id("optimalTerminationRule")), Close,
                    RowBreak, Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("rule"), Comma, Esc,
                    Call("Greatest", F.Id("inlineConsensusModel"), F.Id("rule")),
                    Sp, Rightarrow, Sp,
                    F.Id("rule"), Sp, Eq, Sp, F.Id("optimalTerminationRule"), Close,
                    RowBreak, Sp, Land, Sp,
                    Call("Sound", F.Id("inlineConsensusModel"), F.Id("alwaysAbstain")),
                    RowBreak, Sp, Land, Sp,
                    Call("StrictBelow", F.Id("alwaysAbstain"),
                        F.Id("optimalTerminationRule")),
                    RowBreak, Sp, Land, Sp,
                    Call("StrictBelow", F.Id("optimalTerminationRule"),
                        F.Id("majorityAdmit")),
                    RowBreak, Sp, Land, Sp, Neg,
                    Call("Sound", F.Id("inlineConsensusModel"), F.Id("majorityAdmit"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Sound inlineConsensusModel means that every admitted observation is free of "
                        + "TerminationHazard inlineConsensusModel. The second conjunct says every rule "
                        + "sound for that model is pointwise below optimalTerminationRule. The third "
                        + "says any Greatest rule for that model "
                        + "equals optimalTerminationRule; it does not assert uniqueness for a weaker "
                        + "or differently defined ordering.")),
                    Paragraph(Text(
                        "The remaining four conjuncts make both comparisons substantive. "
                        + "alwaysAbstain is sound and lies strictly below optimalTerminationRule, "
                        + "with safeAdmittedObservation witnessing strictness. majorityAdmit is "
                        + "strictly more permissive than optimalTerminationRule but is not sound; "
                        + "hazardousMajorityObservation witnesses both the strict comparison and "
                        + "the soundness failure.")),
                    Paragraph(Text(
                        "The proof identifies permit observations with an exact roster whose three "
                        + "named results are all satisfied, then uses Mathlib's IsGreatest.unique for "
                        + "the final equality. The proposition is internal to the Lean model and makes "
                        + "no claim about a current or future external plugin version."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("no-carrier-reopened-covers-all-recorded-worker-attempts"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusExecution.NoCarrierReopened"),
                H("No carrier reopened covers all recorded worker attempts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "NoCarrierReopened events is exactly Nodup over workerAttemptHistory events. "
                        + "Event.workerAttemptKeys records the singleton key of a flightFailure, every "
                        + "attempted key carried by an advance, and every attempted key carried by a "
                        + "boundedPass; finish and abstain contribute no keys.")),
                    Paragraph(Text(
                        "The predicate therefore covers failed flights, successful advances, and "
                        + "bounded passes. It is not the older failure-only property."))),
                DescribeRole.Definition),
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
                        + "has a positive attempt number equal to its configured retry budget. "
                        + "workerAttemptHistory has no duplicate FlightKey across failure, advance, "
                        + "and bounded-pass events; the number of bounded-pass events does not exceed "
                        + "the shared-pass budget; and the event-list length does not exceed "
                        + "explicitRunBound config.")),
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
