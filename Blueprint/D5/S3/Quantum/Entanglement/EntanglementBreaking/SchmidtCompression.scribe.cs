using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EntanglementBreaking;

internal sealed class SchmidtCompressionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Schmidt-restricted quadratic bounds imply separable Choi compressions.",
        H("Separable Schmidt compressions"),
        Blocks(
            Describe.Lean(DescribeId.Create("eb-schmidtcompression-schmidtquadraticbound"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/SchmidtCompression.SchmidtQuadraticBound"),
                H("Schmidt-restricted quadratic form bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The bound applies to unit Euclidean vectors whose coefficient matrices have rank at most k."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("eb-schmidtcompression-candidate-compression-separable"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/SchmidtCompression.candidate_compression_separable"),
                H("Separability after rectangular input compression"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A right isometric factorization reduces local congruence to an isometric compression followed by local filtering. The Schmidt-restricted bound controls every unit vector in the isometric compression. The contraction-block separability theorem applies to its scalar shift."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eb-schmidtcompression-candidate-iskeb"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/SchmidtCompression.candidate_isKEB"),
                H("Candidate is keb"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For one at most k at most d, a Hermitian H satisfying the Schmidt-restricted quadratic bound gives a k-entanglement-breaking Choi candidate."))),
                DescribeRole.Theorem))));
}
