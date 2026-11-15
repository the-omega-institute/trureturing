using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianExternalBlocksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Corrected and Inverse-right External Gaussian Blocks",
        H("Actual Corrected and Inverse-right External Gaussian Blocks"),
        Blocks(
            Paragraph(Text("The left row is the literal damped correctedMatrix restricted to a frequency box and any finite external family. The right row is its actual transport by sourceBlock of the inverse frequency Gram boxMatrix. Arbitrary input and output modes, all colours and empty finite supports are included.")),
            Paragraph(Text("Expanding these arrays gives internal blocks G tensor D K D and G inverse tensor D inverse K D inverse. The nondegenerate symmetric Gram and nonzero frequency roots give both ordered inverse similarities to the finite square resolvent. This algebra needs no Gram square-root construction or separate raw-block contraction hypothesis.")),
            Paragraph(Text("Substitution into FiniteGaussianSewing.effectiveKernel gives equal diagonal blocks G times the free input-output covariance plus B_J, cross block minus G times B_T, and its ordinary transpose. Uniform signed and square cutoff estimates and the external l1 bounds prove locally uniform convergence on every smaller complex disk.")),
            Paragraph(Text("The effectiveKernel definition is used algebraically; finite_sewing is not applied outside its raw contraction hypotheses. This covariance theorem makes no claim of raw full-disk occupation summability, source energy coefficient extraction, Laurent selectors, theta averaging, identityK or C1.")),
            Describe.Lean(
                DescribeId.Create("root-units"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.root_units"),
                H("root_units"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The frequency square-root diagonal matrix and its reciprocal multiply to the identity in both orders, including the empty frequency box."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-row"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.originalRow"),
                H("originalRow"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The originalRow definition fixes the literal objects and conventions used in the proof."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("inverse-substitution"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.inverseSubstitution"),
                H("inverseSubstitution"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The inverseSubstitution definition fixes the literal objects and conventions used in the proof."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("left-row"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.leftRow"),
                H("leftRow"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The leftRow definition fixes the literal objects and conventions used in the proof."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("right-row"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.rightRow"),
                H("rightRow"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The rightRow definition fixes the literal objects and conventions used in the proof."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("original-effective-kernel"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.originalEffectiveKernel"),
                H("originalEffectiveKernel"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The originalEffectiveKernel definition fixes the literal objects and conventions used in the proof."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("explicit-effective-kernel"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.explicitEffectiveKernel"),
                H("explicitEffectiveKernel"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The explicitEffectiveKernel definition fixes the literal objects and conventions used in the proof."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("original-source"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.original_source"),
                H("original_source"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original_source statement is verified on its displayed full domain and consumed by the original Gaussian source calculation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-inverse-source"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.original_inverse_source"),
                H("original_inverse_source"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original_inverse_source statement is verified on its displayed full domain and consumed by the original Gaussian source calculation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-internal-inverse-similarities"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.original_internal_inverse_similarities"),
                H("original_internal_inverse_similarities"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original_internal_inverse_similarities statement is verified on its displayed full domain and consumed by the original Gaussian source calculation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-mixed"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.original_mixed"),
                H("original_mixed"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original_mixed statement is verified on its displayed full domain and consumed by the original Gaussian source calculation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-inverse-mixed"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.original_inverse_mixed"),
                H("original_inverse_mixed"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original_inverse_mixed statement is verified on its displayed full domain and consumed by the original Gaussian source calculation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-mixed-transpose"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.original_mixed_transpose"),
                H("original_mixed_transpose"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original_mixed_transpose statement is verified on its displayed full domain and consumed by the original Gaussian source calculation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cutoff-zero-extend"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.cutoff_zeroExtend"),
                H("cutoff_zeroExtend"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cutoff_zeroExtend statement is verified on its displayed full domain and consumed by the original Gaussian source calculation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("external-pair-error"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.external_pair_error"),
                H("external_pair_error"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The external_pair_error statement is verified on its displayed full domain and consumed by the original Gaussian source calculation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-effective-kernel-blocks-tendsto-explicit"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalBlocks.original_effectiveKernel_blocks_tendsto_explicit"),
                H("original_effectiveKernel_blocks_tendsto_explicit"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original_effectiveKernel_blocks_tendsto_explicit statement is verified on its displayed full domain and consumed by the original Gaussian source calculation."))), DescribeRole.Theorem))));
}
