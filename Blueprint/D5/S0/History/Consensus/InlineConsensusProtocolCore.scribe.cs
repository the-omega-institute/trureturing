using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Consensus;

internal sealed class InlineConsensusProtocolCoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite protocol observations, dispatch plans, and fail-closed routers.",
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
                DescribeId.Create("dispatch-plans-carry-layout-proofs"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusProtocolCore.DispatchPlan"),
                H("Dispatch plans carry layout proofs"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A DispatchPlan stores assignments for the thinking, review, and termination "
                        + "seats together with a MultiSeatLayout proof for each assignment. That "
                        + "layout gives isolatedTokenSubagent and nyxidOracle exactly one seat each "
                        + "and gives abstain no seat."))),
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
