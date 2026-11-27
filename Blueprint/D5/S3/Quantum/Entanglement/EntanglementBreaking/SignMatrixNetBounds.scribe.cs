using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EntanglementBreaking;

internal sealed class SignMatrixNetBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        H("Failure probabilities from finite nets"),
        Blocks(
            Describe.Lean(DescribeId.Create("eb-signmatrixnetbounds-signcubesample-schmidt-failure-le"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixNetBounds.signCubeSample_schmidt_failure_le"),
                H("Schmidt bound tail"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Sum the fixed-pair bilinear tail bounds over the Cartesian square of the Schmidt net."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eb-signmatrixnetbounds-operator-tail-of-quadratic-tail"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/SignMatrixNetBounds.operator_tail_of_quadratic_tail"),
                H("Operator norm tail from quadratic tails"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Bound the probability of a norm threshold by the union of fixed-vector quadratic events on a net of the full sphere."))),
                DescribeRole.Theorem))));
}
