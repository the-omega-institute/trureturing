using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EntanglementBreaking;

internal sealed class SignMatrixFailureBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The three finite sign failure bounds at the admissible dimensions.",
        H("Dimension thresholds for the three bad events"),
        Blocks(
            Describe.Lean(DescribeId.Create("eb-signmatrixfailurebounds-schmidt-failure-bound-lt-quarter"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixFailureBounds.schmidt_failure_bound_lt_quarter"),
                H("Schmidt failure bound below one quarter"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For k at least two and d at least 524288 times k cubed, the quadratic tail exponent dominates the logarithmic net-size contribution with strict margin."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eb-signmatrixfailurebounds-operator-failure-bound-lt-quarter"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixFailureBounds.operator_failure_bound_lt_quarter"),
                H("Operator failure bound below one quarter"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For d at least four, the exponent for threshold 3d dominates the logarithmic sphere-net contribution. This numerical bound is used for both operator events."))),
                DescribeRole.Theorem))));
}
