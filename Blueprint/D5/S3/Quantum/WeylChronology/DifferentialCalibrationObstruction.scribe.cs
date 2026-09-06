using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.WeylChronology;

internal sealed class DifferentialCalibrationObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/WeylChronology/DifferentialCalibrationObstruction.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Radius-form consumers of the sharp differential-calibration ambiguity theorem.",
        H("Differential calibration obstruction"),
        Blocks(
            Paragraph(Text("The general proofs are owned by ClosedPathChronologyAmbiguity. This document describes five existing radius-form companion declarations that now import that owner. They are applications and algebraic presentations, with no additional novelty claim. Lean compilation and Scribe emission remain unverified.")),
            Paragraph(Text("The hidden object includes a history and its admissible unknown error record. Only completed actions at a fixed setting are compared. Additional reference controls, intermediate measurements, and a single common nuisance model are distinct experiments.")),
            Describe.Lean(DescribeId.Create("zero-total-error-phase"),
                DeclarationHandle.Create(Prefix + "zero_total_error_phase"),
                H("A closed endpoint with a central error"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Directly consumes closed_error_phase. Opposite half-errors cancel the residual displacement but leave the phase Y ux - X uy."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("zero-total-phase-radius"),
                DeclarationHandle.Create(Prefix + "zero_total_phase_radius_iff"),
                H("Exact single-record phase radius"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Consumes bounded_closed_phase_iff with squared budget radius squared. The attaining vector and lower bound are proved by that owner. The algebraic statement permits either sign of radius; its physical interpretation uses a nonnegative radius."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("two-record-phase-radius"),
                DeclarationHandle.Create(Prefix + "two_record_phase_alias_iff"),
                H("Sharp unwrapped two-record alias"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Consumes bounded_real_phase_collision_iff. Both hypotheses may use different admissible nuisance records. The converse concerns unwrapped real phases and does not exclude additional aliases modulo two pi."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("zero-total-action-normal-form"),
                DeclarationHandle.Create(Prefix + "zero_total_control_normal_form"),
                H("The literal completed action"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Consumes closed_error_word_normal_form and closed_error_phase, then expands the real phase by ring normalization. No action, Gaussian overlap, or Born-law definition is duplicated."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("closed-endpoint-operator-alias"),
                DeclarationHandle.Create(Prefix + "closed_endpoint_operator_alias"),
                H("Equal final actions with different histories"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Consumes same_inventory_bounded_action_collision with squared budget radius squared. It preserves the complete-action conclusion on every input function. All five declarations are bind-only companions; no new recovery guarantee, experiment, quantum advantage, or kernel-verification claim is made."))), DescribeRole.Theorem))));
}
