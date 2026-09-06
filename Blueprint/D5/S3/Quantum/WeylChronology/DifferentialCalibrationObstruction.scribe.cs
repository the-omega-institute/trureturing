using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.WeylChronology;

internal sealed class DifferentialCalibrationObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/WeylChronology/DifferentialCalibrationObstruction.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Perfect endpoint closure does not certify chronology identification under differential errors.",
        H("Differential calibration obstruction"),
        Blocks(
            Paragraph(Text("This is a candidate source. The state object includes a history and its admissible unknown error record. Only completed actions are compared; additional reference controls or intermediate measurements are separate observations.")),
            Describe.Lean(DescribeId.Create("zero-total-error-phase"),
                DeclarationHandle.Create(Prefix + "zero_total_error_phase"),
                H("A closed endpoint with a central error"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Opposite half-errors cancel the residual displacement but leave the phase Y ux - X uy."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("zero-total-phase-radius"),
                DeclarationHandle.Create(Prefix + "zero_total_phase_radius_iff"),
                H("Exact single-record phase radius"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Cauchy-Schwarz supplies necessity. The explicit vector parallel to (Y,-X) attains the bound. Radius is expressed in squared Euclidean units."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("two-record-phase-radius"),
                DeclarationHandle.Create(Prefix + "two_record_phase_alias_iff"),
                H("Sharp unwrapped two-record alias"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both hypotheses may use different admissible nuisance records. The real phase intervals intersect exactly at the stated radius. The converse does not exclude additional aliases modulo 2 pi."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("zero-total-action-normal-form"),
                DeclarationHandle.Create(Prefix + "zero_total_control_normal_form"),
                H("The literal completed action"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing splitCompensatedWord acts as a pure phase on every wavefunction when its errors sum to zero. No new Weyl action or overlap law is introduced."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("closed-endpoint-operator-alias"),
                DeclarationHandle.Create(Prefix + "closed_endpoint_operator_alias"),
                H("Equal final actions with different histories"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For same-inventory histories and the specified calibration budget, explicit admissible error records make the completed physical actions identical on every input. Endpoint closure and Gaussian attenuation alone cannot detect this ambiguity. No experimental result, quantum advantage or completed Lean compilation is asserted."))), DescribeRole.Theorem))));
}
