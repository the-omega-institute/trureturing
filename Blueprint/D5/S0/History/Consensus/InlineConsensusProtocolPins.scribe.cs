using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Consensus;

internal sealed class InlineConsensusProtocolPinsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Concrete fixtures pin selector-backed worker-mode routing, recoverable permit freshness, identity-sensitive snapshots, and model-indexed clause coverage.",
        H("Inline Consensus Protocol Pins"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-protocol-initial-plan-is-compatible"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusProtocolPins."
                    + "protocol_initial_plan_is_compatible"),
                H("The protocol initial plan is compatible"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("InitialPlanCompatible", F.Id("protocolEligibility"),
                        F.Id("protocolDispatchPlan"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "protocolDispatchPlan assigns an implementation carrier as well as the three "
                        + "multi-seat functions. This theorem proves that every carrier returned by "
                        + "its carrierAt function is legal for that stage and role and is accepted by "
                        + "protocolEligibility."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a-mismatched-initial-plan-is-rejected"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusProtocolPins."
                    + "mismatched_initial_plan_is_rejected"),
                H("A mismatched initial plan is rejected"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("mismatchedImplementationEligibility", F.Id("implementationWorker"),
                        F.Id("implementation"), F.Id("codexCli")),
                    Sp, Eq, Sp, F.Id("false"),
                    RowBreak, Sp, Land, Sp,
                    Call("mismatchedImplementationEligibility", F.Id("implementationWorker"),
                        F.Id("implementation"), F.Id("nyxidOracle")),
                    Sp, Eq, Sp, F.Id("true"),
                    RowBreak, Sp, Land, Sp, Neg,
                    Call("InitialPlanCompatible", F.Id("mismatchedImplementationEligibility"),
                        F.Id("protocolDispatchPlan"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At the implementationWorker/implementation position, the mismatched "
                        + "eligibility function rejects codexCli and accepts nyxidOracle. Because "
                        + "protocolDispatchPlan assigns codexCli there, the same theorem's third "
                        + "conjunct proves that this eligibility function and plan are not "
                        + "InitialPlanCompatible."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-distinct-complete-goal-artifacts-exist"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusProtocolPins."
                    + "two_distinct_complete_goal_artifacts_exist"),
                H("Two distinct complete goal artifacts exist"),
                StatementSource.FromAuthor(Disp(Seq(
                    Exists, Sp, F.Id("first"), Comma, Sp, F.Id("second"), Colon, Sp,
                    F.Id("GoalArtifact"), Comma, Esc,
                    Field(F.Id("first"), "Complete"), Sp, Land, Sp,
                    Field(F.Id("second"), "Complete"), Sp, Land, Sp,
                    F.Id("first"), Sp, Neq, Sp, F.Id("second")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The witnesses are protocolGoalArtifact, whose seven optional digest fields "
                        + "contain digestA, and protocolAlternateGoalArtifact, whose rawUserInput "
                        + "contains digestB. Both satisfy GoalArtifact.Complete, but the artifacts "
                        + "are unequal. The theorem is existential and does not classify all complete "
                        + "artifacts."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-complete-goal-snapshot-is-accepted"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusProtocolPins."
                    + "complete_goal_snapshot_is_accepted"),
                H("The complete goal snapshot is accepted"),
                StatementSource.FromAuthor(Disp(Seq(
                    ContainsComplete(F.Id("protocolGoalArtifact"),
                        Snapshot(F.Id("protocolGoalArtifact"), FinsetUniv()))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The snapshot contains protocolGoalArtifact itself and exposes Finset.univ. "
                        + "The theorem proves ContainsComplete for that shared artifact and exactly "
                        + "that full snapshot."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a-full-snapshot-with-the-wrong-artifact-is-rejected"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusProtocolPins."
                    + "full_snapshot_with_wrong_artifact_is_rejected"),
                H("A full snapshot with the wrong artifact is rejected"),
                StatementSource.FromAuthor(Disp(Seq(
                    Neg, Sp, ContainsComplete(F.Id("protocolGoalArtifact"),
                        Snapshot(F.Id("protocolAlternateGoalArtifact"),
                            FinsetUniv()))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Although the snapshot exposes Finset.univ and its alternate artifact is "
                        + "complete, ContainsComplete also requires artifact identity with the shared "
                        + "protocolGoalArtifact. The alternate rawUserInput digest makes that equality "
                        + "false."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("empty-visible-fields-are-rejected"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusProtocolPins."
                    + "empty_visible_fields_are_rejected"),
                H("Empty visible fields are rejected"),
                StatementSource.FromAuthor(Disp(Seq(
                    Neg, Sp, ContainsComplete(F.Id("protocolGoalArtifact"),
                        Snapshot(F.Id("protocolGoalArtifact"), Varnothing))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "This snapshot carries the correct complete artifact but has no visible "
                        + "fields. It is rejected because ContainsComplete requires visibleFields to "
                        + "equal Finset.univ."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("worker-mode-advance-consumes-selection-and-availability-evidence"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusProtocolPins."
                    + "worker_mode_advance_consumes_selector_and_availability"),
                H("Worker-mode advance consumes selection and availability evidence"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("model"), Comma, Esc,
                    Call("WorkerModeAdvanceConsumesSelection", F.Id("model"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "WorkerModeAdvanceConsumesSelection model quantifies over an advance from "
                        + "chooseWorkerMode to thinkingPanelWorkers. Every such model.transition yields "
                        + "a carrier selected by model.fallbackSelector from workerModeEligibility and "
                        + "the empty tried set, together with evidence that the selected carrier is "
                        + "available and is not abstain.")),
                    Paragraph(Text(
                        "The theorem does not say that an advance exists for every configuration; it "
                        + "extracts the three pieces of evidence from an advance transition that already "
                        + "exists."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("before-launch-fallback-and-empty-history-abstention-are-pinned"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusProtocolPins."
                    + "concrete_choose_worker_mode_routing_is_pinned"),
                H("Before-launch fallback and empty-history abstention are pinned"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("ConcreteChooseWorkerModeRouting", F.Id("inlineConsensusModel"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "ConcreteChooseWorkerModeRouting inlineConsensusModel first records that "
                        + "nyxidOnlyAvailable rejects codexCli, accepts nyxidOracle, and makes the "
                        + "model's fallbackSelector choose nyxidOracle from an empty tried set.")),
                    Paragraph(Text(
                        "Its final conjunct supplies an abstain transition at chooseWorkerMode for the "
                        + "noWorkerAvailable configuration. The resulting state is abstained, its "
                        + "attemptedFlights set is empty, and workerAttemptHistory for that abstain "
                        + "event is the empty list. This is a before-launch pin, not a claim about a "
                        + "later failed flight."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("stale-permit-rejection-and-fresh-reevaluation-are-pinned"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusProtocolPins."
                    + "stale_permit_cannot_finish_and_fresh_evaluation_is_reachable"),
                H("Stale-permit rejection and fresh reevaluation are pinned"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("ConcretePermitRecovery", F.Id("inlineConsensusModel"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "ConcretePermitRecovery inlineConsensusModel supplies a reevaluated state for "
                        + "the named permitInvalidatedState. It states that this state has no "
                        + "terminationExit, does not satisfy FinishPrecondition, and has an outgoing "
                        + "terminationGate transition using freshTerminationObservation.")),
                    Paragraph(Text(
                        "The fixture defines permitInvalidatedState with recordEvent after an intervening "
                        + "flight failure, and intervening_failure_clears_current_permit separately proves "
                        + "that invalidating ProtocolStep. The recovery theorem does not claim that the "
                        + "fresh evaluation's result is permitClaim."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-inline-consensus-model-models-every-clause"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusProtocolPins."
                    + "inline_consensus_model_models_every_clause"),
                H("The inline-consensus model models every clause"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("clause"), Comma, Esc,
                    Call("ModelsClause", F.Id("inlineConsensusModel"), F.Id("clause"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The theorem states forall clause, ModelsClause inlineConsensusModel clause. "
                        + "ClauseId has ten constructors, and ModelsClause is a function of the governing "
                        + "model whose branches state the corresponding indexed protocol obligations.")),
                    Paragraph(Text(
                        "For inlineConsensusModel the ten branches include the stage algebra, selector "
                        + "and dispatch obligations, retry commitments, completion evidence, absorbing "
                        + "abstention, isolation and artifact conditions, the S7 independence contrast, "
                        + "model-routed transition witnesses, termination safety and freshness, and "
                        + "shared-budget bounds. This theorem is clause coverage for this concrete model; "
                        + "it does not assert ModelsClause for every InlineConsensusModel."))),
                DescribeRole.Theorem))));

    private static Formula Field(Formula subject, string field) =>
        Seq(subject, Dot, F.Id(field));

    private static Formula ContainsComplete(Formula shared, Formula snapshot) =>
        Seq(F.Id("GoalArtifactSnapshot"), Dot,
            Call("ContainsComplete", shared, snapshot));

    private static Formula FinsetUniv() =>
        Seq(F.Id("Finset"), Dot, F.Id("univ"));

    private static Formula Snapshot(Formula artifact, Formula visibleFields) =>
        Seq(Langle, Sp, artifact, Comma, Sp, visibleFields, Rangle);
}
