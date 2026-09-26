using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Thermal;

internal sealed class HiddenExperimentRiskDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local Kraus histories preserve the actual hidden tensor factor. The indistinguishable-output estimation problem has matching lower and attained upper absolute-risk bounds.",
        H("Hidden Experiments and Sharp Absolute Risk"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("branch-product"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/HiddenExperimentRisk.branch_product"),
                H("A local Kraus update preserves the hidden factor"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The statement uses complex matrices and actual Kronecker products. Unnormalised branches avoid division by zero-probability events."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("adaptive-record-product"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/HiddenExperimentRisk.adaptive_record_product"),
                H("Full adaptive history induction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The policy takes the complete previous record as input. Every finite branch remains the visible updated matrix tensored with the unchanged hidden state."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hidden-states-indistinguishable"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/HiddenExperimentRisk.hidden_states_indistinguishable"),
                H("Hidden trace-one states have identical record weights"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Equality is proved for the entire finite-record weight function. Quantum instrument positivity and normalization restrict to a physical subclass without altering this equality; their construction is not claimed here."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("endpoint-risk-sum"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/HiddenExperimentRisk.endpoint_risk_sum"),
                H("Endpoint lower bound for arbitrary randomized output"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The estimator output is an arbitrary probability measure on the real line. Nonnegative integration retains infinite risks instead of assigning a zero Bochner integral to a nonintegrable loss."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sharp-no-information-risk"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/HiddenExperimentRisk.sharp_no_information_risk"),
                H("Matching randomized lower and midpoint upper bounds"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every interval of diameter L, every common output law has worst endpoint absolute risk at least L/2, and the point mass at the midpoint attains the uniform upper bound. Identification of the full quantum entropy range is a separate obligation."))), DescribeRole.Theorem))));
}
