using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.CausalMoments;

internal sealed class SparseFixedNoiseBenefitRealizationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/CausalMoments/SparseFixedNoiseBenefitRealization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compress the two complete table laws separately and retain their product semantics. The full selected-pair response distribution is unchanged, so every previously attainable benefit value has a sparse independent witness.",
        H("Sparse fixed-noise benefit realization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sparse-fixed-noise-equivalent"),
                DeclarationHandle.Create(Prefix + "exists_fixedNoise_sparse_equivalent"),
                H("Separate compression preserves the selected law"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both mechanisms retain every complete row marginal. Each has at most 3k+1 nonzero table atoms, and the joint distribution of the covariate and selected responses remains equal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pair-support-card"),
                DeclarationHandle.Create(Prefix + "fixedNoise_pair_support_card_le"),
                H("Bound the product disturbance support"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The support of the rational product law is the Cartesian product of the component supports. The two-mechanism support is at most the square of 3k+1; the covariate root is separate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-attainment-iff"),
                DeclarationHandle.Create(Prefix + "fixedNoise_sparse_attainment_iff"),
                H("Preserve the entire attainable query image"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A target with the four prescribed conditional intervention marginals is attainable exactly when it is attainable with both table support bounds. No extra cross-stratum constraints are supplied."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sparse-sharp-iff"),
                DeclarationHandle.Create(Prefix + "fixedNoise_sparse_joint_benefit_sharp_iff"),
                H("Sparse attaining witnesses for the sharp interval"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Composes the prior weighted-product sharp interval theorem with the new same-model-family support reduction. The interval, marginal conditions, and benefit definition are unchanged."))),
                DescribeRole.Theorem))));
}
