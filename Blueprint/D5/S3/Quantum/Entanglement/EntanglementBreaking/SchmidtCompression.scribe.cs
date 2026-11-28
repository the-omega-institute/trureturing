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
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For 1 ≤ k ≤ d, the Schmidt-restricted bound controls every unit vector in the compression of the candidate to an isometric k-dimensional input subspace. The contraction-block separability theorem applies to the shifted compression."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eb-schmidtcompression-candidate-iskeb"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/SchmidtCompression.candidate_isKEB"),
                H("The map defined by the Choi candidate is k-entanglement-breaking"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For 1 ≤ k ≤ d and Hermitian H satisfying the Schmidt-restricted quadratic bound, the map with input-first Choi matrix I − (16/d)H is k-entanglement-breaking. A right isometric factorization transfers separability from the isometric compression to every rectangular local congruence."))),
                DescribeRole.Theorem))));
}
