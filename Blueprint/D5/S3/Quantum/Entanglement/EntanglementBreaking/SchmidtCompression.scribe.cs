using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EntanglementBreaking;

internal sealed class SchmidtCompressionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        H("Separable Schmidt compressions"),
        Blocks(
            Describe.Lean(DescribeId.Create("eb-schmidtcompression-schmidtquadraticbound"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/SchmidtCompression.SchmidtQuadraticBound"),
                H("Schmidt-restricted quadratic form bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The bound applies to unit Euclidean vectors whose coefficient matrices have rank at most k."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("eb-schmidtcompression-candidate-compression-separable"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/SchmidtCompression.candidate_compression_separable"),
                H("Separability after rectangular input compression"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A right isometric factorization reduces local congruence to an isometric compression followed by local filtering. The Schmidt-restricted bound controls every unit vector in the isometric compression. The contraction-block separability theorem applies to its scalar shift."))),
                DescribeRole.Theorem))));
}
