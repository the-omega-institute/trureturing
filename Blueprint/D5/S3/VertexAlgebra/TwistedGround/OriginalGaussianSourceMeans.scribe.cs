using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianSourceMeansDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original Opposite-charge Means and Constant",
        H("Original Opposite-charge Means and Constant"),
        Blocks(
            Paragraph(Text("The full complex source column is consumed in absolutely convergent central-binomial series U and S. U pairs an actual binomial external column with the inverse source column. S is the unweighted source pairing; it is distinct from the weighted scalar moment.")),
            Paragraph(Text("The finite left mean is the damped correctedMean. The right mean is the actual inverse-right source transport of charge minus a. The same finite inverse similarities reduce their eliminated internal vectors to the finite one-minus resolvent source column. Ordinary bilinear colour contraction yields left mean (G a)_j times (-1 + U), right mean (G a)_j times (1 - U), and constant chargeNorm(a) times S.")),
            Paragraph(Text("The constant is the half-sum of all four entries of the two-auxiliary effective covariance. Norm convergence of source and external cutoffs, with uniform signed-resolvent estimates, proves locally uniform convergence of the actual finite means and constant on every smaller disk.")),
            Paragraph(Text("These are repository-derived Gaussian source identities. The original fixed-energy coefficient theorem, both Laurent selectors and charge factors, theta half-average and cross-channel identityK and C1 remain separate scientific obligations. No ungrouped occupation-series assertion on the full disk is made.")),
            Describe.Lean(
                DescribeId.Create("source-external"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceMeans.sourceExternal"),
                H("sourceExternal"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sourceExternal definition fixes the literal objects and conventions used in the proof."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("source-constant"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceMeans.sourceConstant"),
                H("sourceConstant"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sourceConstant definition fixes the literal objects and conventions used in the proof."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("left-mean"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceMeans.leftMean"),
                H("leftMean"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The leftMean definition fixes the literal objects and conventions used in the proof."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("right-mean"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceMeans.rightMean"),
                H("rightMean"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The rightMean definition fixes the literal objects and conventions used in the proof."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("effective-mean"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceMeans.effectiveMean"),
                H("effectiveMean"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The effectiveMean definition fixes the literal objects and conventions used in the proof."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("effective-constant"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceMeans.effectiveConstant"),
                H("effectiveConstant"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The effectiveConstant definition fixes the literal objects and conventions used in the proof."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("source-pairings-explicit"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceMeans.source_pairings_explicit"),
                H("source_pairings_explicit"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The source_pairings_explicit statement is verified on its displayed full domain and consumed by the original Gaussian source calculation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-opposite-charge-means-explicit"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceMeans.original_opposite_charge_means_explicit"),
                H("original_opposite_charge_means_explicit"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original_opposite_charge_means_explicit statement is verified on its displayed full domain and consumed by the original Gaussian source calculation."))), DescribeRole.Theorem))));
}
