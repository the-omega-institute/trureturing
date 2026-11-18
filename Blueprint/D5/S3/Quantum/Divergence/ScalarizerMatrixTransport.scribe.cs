using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class ScalarizerMatrixTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rectangular matrix transports for the common positive-state scalarizer.",
        H("Rectangular Euclidean matrix transports"), Blocks(
            Describe.Lean(DescribeId.Create("gram-majorization"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/ScalarizerMatrixTransport.gram_majorization"),
                H("Gram order and adjoint norm"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The positive semidefinite inequality k C C adjoint minus D D adjoint bounds the norm of D adjoint z by square root k times the norm of C adjoint z. It applies to different column spaces and to k=0."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("matrix-clm-adjoint"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/ScalarizerMatrixTransport.matrixCLM_adjoint"),
                H("Adjoint transport"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Euclidean continuous linear map of a conjugate transpose is the adjoint of the Euclidean continuous linear map. The rectangular factor and the supported Gram estimate use this identity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rectangular-douglas"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/ScalarizerMatrixTransport.rectangular_douglas"),
                H("A rectangular factor with the prescribed bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Pad the two rectangular maps on the Euclidean Hilbert space over the disjoint sum of their column indices. The existing Douglas majorization theorem supplies an operator on that Hilbert space. Its off-diagonal block is a factor T with C T=D and norm at most square root k. Restriction and inclusion preserve the bound, including k=0. The common positive-state theorem applies this factor to its selected joint Gram."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("matrix-clm-mul"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/ScalarizerMatrixTransport.matrixCLM_mul"),
                H("Composition transport"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Euclidean continuous linear maps carry matrix multiplication to composition. The projection of the rectangular factor uses this identity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("norm-bound-gram"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/ScalarizerMatrixTransport.norm_bound_gram"),
                H("Norm bounds as Gram order"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A pointwise square root k norm bound implies positivity of k I minus T adjoint T. The common-state construction uses this estimate for the rectangular factor, the singular polar contraction and the supported Gram flip."))), DescribeRole.Theorem))));
}
