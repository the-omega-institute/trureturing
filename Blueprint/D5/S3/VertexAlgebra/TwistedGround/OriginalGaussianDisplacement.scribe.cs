using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianDisplacementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered Displacement on the Original Gaussian Carrier",
        H("Ordered Displacement on the Original Gaussian Carrier"),
        Blocks(
            Paragraph(Text("The original signed Cauchy matrix is symmetric for ordinary complex transpose. Multiplication by the frequency diagonal is confined to finite matrices. Its anticommutator is the outer product of the actual weighted source.")),
            Paragraph(Text("The two ordered inverse identities are proved with genuine units. Signed Neumann cutoffs agree with the finite inverses on zero-extended vectors, while retaining the identity on the complementary infinite subspace. The signed uniform cutoff and source norm limits pass both identities to each fixed coordinate of the original square-summable carrier.")),
            Paragraph(Text("This is classical finite displacement algebra and repository-derived norm convergence, with no assertion of a bounded frequency diagonal on the entire infinite carrier.")),
            Describe.Lean(
                DescribeId.Create("section-symm"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDisplacement.section_symm"),
                H("section_symm"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The section_symm statement is verified on its displayed full domain and consumed by the original Gaussian source calculation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-extend-signed"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDisplacement.zeroExtend_signed"),
                H("zeroExtend_signed"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The zeroExtend_signed statement is verified on its displayed full domain and consumed by the original Gaussian source calculation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("section-zero-extend"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDisplacement.section_zeroExtend"),
                H("section_zeroExtend"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The section_zeroExtend statement is verified on its displayed full domain and consumed by the original Gaussian source calculation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-extend-square-inverse"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDisplacement.zeroExtend_square_inverse"),
                H("zeroExtend_square_inverse"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The zeroExtend_square_inverse statement is verified on its displayed full domain and consumed by the original Gaussian source calculation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signed-resolvent-displacement"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDisplacement.signed_resolvent_displacement"),
                H("signed_resolvent_displacement"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The signed_resolvent_displacement statement is verified on its displayed full domain and consumed by the original Gaussian source calculation."))), DescribeRole.Theorem))));
}
