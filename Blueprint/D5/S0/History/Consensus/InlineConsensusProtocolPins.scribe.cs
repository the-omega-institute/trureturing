using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Consensus;

internal sealed class InlineConsensusProtocolPinsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Concrete dispatch and goal-artifact fixtures pin initial-plan compatibility, identity-sensitive snapshots, and every indexed protocol clause.",
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
                DescribeId.Create("the-required-inline-consensus-fixture-suite-is-pinned"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusProtocolPins."
                    + "required_fixture_suite_is_pinned"),
                H("The required inline-consensus fixture suite is pinned"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("clause"), Comma, Esc,
                    Call("ClauseObject", F.Id("clause"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "RequiredFixtureSuite unfolds to forall clause, ClauseObject clause. ClauseId "
                        + "has ten constructors, and every ClauseObject branch contains the full "
                        + "semantic conjunction for that indexed protocol clause.")),
                    Paragraph(Text(
                        "The proof supplies every conjunct and now consumes the stage-successor, "
                        + "carrier-selection, initial-plan, fallback, run, router, artifact, permit, "
                        + "and budget theorems used by the ten cases. It also discharges the remaining "
                        + "layout and transition-preservation obligations locally; those local proofs "
                        + "are not additional public declarations."))),
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
