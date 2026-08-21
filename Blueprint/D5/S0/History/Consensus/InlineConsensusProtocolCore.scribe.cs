using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Consensus;

internal sealed class InlineConsensusProtocolCoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite protocol observations, digest-valued goal artifacts, implementation-aware dispatch plans, and fail-closed routers.",
        H("Inline Consensus Protocol Core"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("carrier-completion-observations"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusProtocolCore.CompletionObservation"),
                H("Carrier completion observations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "CompletionObservation has three constructors: codex records five Boolean "
                        + "fields for carrier exit, result artifact, envelope, verdict, and sentinel; "
                        + "nyxid records three Boolean fields for terminal status, envelope, and "
                        + "verdict; and subagent records Boolean envelope and verdict fields."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("goal-artifacts-carry-seven-optional-digests"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusProtocolCore.GoalArtifact"),
                H("Goal artifacts carry seven optional digests"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "GoalArtifact has seven fields: rawUserInput, normalizedGoal, constraints, "
                        + "successCriteria, iterationQuestion, harness, and revisions. Each field "
                        + "has type Option GoalArtifactDigest, and GoalArtifactDigest has the two "
                        + "distinct constructors digestA and digestB; these fields are not Booleans.")),
                    Paragraph(Text(
                        "GoalArtifact.Complete checks that all seven options are present. "
                        + "GoalArtifactSnapshot.ContainsComplete additionally requires the snapshot's "
                        + "artifact to equal the shared artifact and its visibleFields to equal "
                        + "Finset.univ."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("dispatch-plans-carry-layout-proofs"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusProtocolCore.DispatchPlan"),
                H("Dispatch plans carry layout proofs"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A DispatchPlan stores a thinking-seat assignment, one implementation "
                        + "carrier, a review-seat assignment, and a termination-seat assignment. "
                        + "It carries a MultiSeatLayout proof for each of the three multi-seat "
                        + "assignments, not for the single implementation carrier. Each layout "
                        + "gives isolatedTokenSubagent and nyxidOracle exactly one seat and gives "
                        + "abstain no seat."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("thinking-results-are-classified-fail-closed"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusProtocolCore.thinkingSituation"),
                H("Thinking results are classified fail closed"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "thinkingSituation returns singlePerspective if any report is presented as "
                        + "consensus. Otherwise it returns unanimousActionable only when all six "
                        + "verdicts propose the same recorded plan, and compatiblePlans only when all "
                        + "six plans are present, pairwise compatible, not all equal, and no verdict "
                        + "rejects or abstains. Every remaining input returns boundedStall."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("review-routing-has-reject-precedence"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusProtocolCore.reviewRouter"),
                H("Review routing has reject precedence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "reviewRouter returns fix when any of the three review verdicts is reject. "
                        + "With no reject it returns done when any verdict is approve, and otherwise "
                        + "returns userDecisionOrBoundedPass."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("termination-routing-requires-an-exact-roster"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusProtocolCore.terminationRouter"),
                H("Termination routing requires an exact roster"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "terminationRouter rejects a non-exact roster as rejectFakeConsensus. For an "
                        + "exact roster it returns permitClaim when all three results are satisfied, "
                        + "continueAgainstGap when some result is unsatisfied but not all are "
                        + "satisfied, and escalateEvidenceGap otherwise."))),
                DescribeRole.Definition))));
}
