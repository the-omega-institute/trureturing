using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianUniformCutoffDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original Gaussian Compact Uniform Cutoffs",
        H("Original Gaussian Compact Uniform Cutoffs"),
        Blocks(
            Paragraph(Text("Principal square sections converge in operator norm uniformly on every smaller closed disk. The original weighted source truncations converge uniformly in the literal complex l2 carrier. Resolvent identities control both signed Neumann inverses and the inverse of one minus the square of the finite section. Squaring occurs after cutoff; no compression of the infinite square is substituted.")),
            Paragraph(Text("These are analytic identities for the original coefficient model on its infinite carrier. Physical vertex operator algebras, conformal field theory, anomaly and fusion structures, string theory and AdS/CFT realization remain open.")),
            Describe.Lean(
                DescribeId.Create("section-op-tendsto-uniformly-on"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.sectionOp_tendstoUniformlyOn"),
                H("sectionOp_tendstoUniformlyOn"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual principal square section operators converge uniformly in operator norm on every smaller closed complex disk."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("trace-weighted-term"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.traceWeightedTerm"),
                H("traceWeightedTerm"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original weighted source coordinate embedded by lp.single into the existing carrier."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weighted-cutoff"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.weightedCutoff"),
                H("weightedCutoff"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The first N terms of the original weighted source on the same infinite carrier."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("trace-weighted-term-tsum"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.traceWeightedTerm_tsum"),
                H("traceWeightedTerm_tsum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The norm-summable embedded coordinate series equals the existing weightedSource for every nonnegative radius below one."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-cutoff-tendsto-uniformly"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.weightedCutoff_tendstoUniformly"),
                H("weightedCutoff_tendstoUniformly"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Weighted cutoffs converge uniformly in l2 on each nonnegative compact radial interval below one."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-cutoff-norm-le"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.weightedCutoff_norm_le"),
                H("weightedCutoff_norm_le"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every weighted cutoff has norm bounded by the enclosing-radius majorant mass."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("trace-neumann-norm-le"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.traceNeumann_norm_le"),
                H("traceNeumann_norm_le"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A norm-contractive operator has Neumann-series norm at most the reciprocal of one minus its norm bound."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("section-signed-resolvent"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.sectionSignedResolvent"),
                H("sectionSignedResolvent"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The genuine signed finite-section Neumann inverse embedded on the original infinite carrier."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("section-signed-resolvent-error"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.sectionSignedResolvent_error"),
                H("sectionSignedResolvent_error"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both unit-modulus signs obey an operator-norm error estimate proportional to the actual section error."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("section-signed-resolvent-tendsto-uniformly-on"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.sectionSignedResolvent_tendstoUniformlyOn"),
                H("sectionSignedResolvent_tendstoUniformlyOn"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The genuine signed section inverses converge uniformly on smaller disks, including signs plus one and minus one."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("section-square-resolvent-error"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.sectionSquareResolvent_error"),
                H("sectionSquareResolvent_error"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The inverse of one minus the square of the actual finite section has an explicit section-error bound."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("section-square-resolvent-tendsto-uniformly-on"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformCutoff.sectionSquareResolvent_tendstoUniformlyOn"),
                H("sectionSquareResolvent_tendstoUniformlyOn"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual finite-square inverses converge uniformly on every smaller disk."))), DescribeRole.Theorem))));
}
