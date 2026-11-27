using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EntanglementBreaking;

internal sealed class SignMatrixNetBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite net bounds for Schmidt and operator tails of Hermitian sign matrices.",
        H("Failure probabilities from finite nets"),
        Blocks(
            Describe.Lean(DescribeId.Create("eb-signmatrixnetbounds-signcubesample-schmidt-failure-le"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixNetBounds.signCubeSample_schmidt_failure_le"),
                H("Schmidt bound tail"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Sum the fixed-pair bilinear tail bounds over the Cartesian square of the Schmidt net."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eb-signmatrixnetbounds-operator-tail-of-quadratic-tail"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixNetBounds.operator_tail_of_quadratic_tail"),
                H("Operator norm tail from quadratic tails"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Bound the probability of a norm threshold by the union of fixed-vector quadratic events on a net of the full sphere."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eb-signmatrixnetbounds-signcubesample-operator-tail"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixNetBounds.signCubeSample_operator_tail"),
                H("Sign cube sample operator tail"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every nonnegative threshold, the ordinary sign matrix operator tail follows from the finite full-sphere net and the fixed-vector quadratic tail."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eb-signmatrixnetbounds-signcubesample-partialtranspose-operator-tail-of-quadratic"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixNetBounds.signCubeSample_partialTranspose_operator_tail_of_quadratic"),
                H("Sign cube sample partial transpose operator tail of quadratic"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The same finite net converts a uniform fixed-vector quadratic tail for the partial transpose into an operator tail for the partial transpose."))),
                DescribeRole.Theorem))));
}
