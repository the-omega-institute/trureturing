using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianDeterminantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original Gaussian Determinant and Cutoff Limit",
        H("Original Gaussian Determinant and Cutoff Limit"),
        Blocks(
            Paragraph(Text("The determinant uses the literal signed entries of OriginalGaussianMatrix and the complex square-summable operator and square cutoffs of OriginalGaussianResolvent. Coordinate n represents the positive frequency n+1. The cutoff is the actual finiteSection N z, including N=0.")),
            Paragraph(Text("The closed-cycle logarithm uses the actual signed entries at positive frequencies, with even walk length 2*(k+1) and divisor k+1. Absolute values are taken on each edge before summing internal vertices. At the negative real radius, the original signs cancel and realize these absolute walks by the same original operator. Its norm bound and a summable geometric coordinate majorant control all cycle lengths. The determinant gaussianDet is the exponential of this absolutely convergent cycle logarithm.")),
            Paragraph(Text("The finite logarithm uses traces of powers of the literal finiteSection N z. Exact zero extension identifies these powers with sectionOp powers, and dominated convergence first passes the spatial cutoff through the coordinate trace, then through the cycle-length series. For real z, one Hermitian spectral eigenbasis works simultaneously for all powers. The actual spectral norm bound and the scalar logarithm series give det(1-(finiteSection N z)^2)=exp(finiteLog N z), including N=0. Polynomial finite entries and a local summable series majorant prove finite-log holomorphy; the identity theorem extends this equality to every complex z with norm(z)<1. Consequently the literal finite determinants converge pointwise to gaussianDet. The square is taken after cutoff.")),
            Paragraph(Text("The infinite signed-cycle logarithm has a direct holomorphy argument on the open unit disk. Polynomial signed entries and a summable geometric bound control the internal-vertex sum by induction on walk length. A second geometric envelope controls the infinite diagonal trace at each positive even length, and the cycle-length majorant controls the logarithm series. Each bound is uniform on a smaller disk containing the evaluation point. Exponentiation then gives holomorphy of gaussianDet; this argument does not require uniform spatial cutoff convergence.")),
            Paragraph(Text("Uniform spatial cutoff convergence, identification with a period expression, and physical or string-theoretic realization are not asserted. The spectral and analytic ingredients are classical; these results are the source-specific composition for the original signed kernel.")),
            Describe.Lean(
                DescribeId.Create("gaussian-log-det"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.gaussianLogDet"),
                H("gaussianLogDet"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Minus the sum of the actual even closed-cycle traces divided by k+1. On norm(z)<1 the series converges absolutely."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gaussian-det"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.gaussianDet"),
                H("gaussianDet"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complex exponential of gaussianLogDet. The cutoff theorem identifies it with the limit of the actual finite Gaussian determinants."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-log"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.finiteLog"),
                H("finiteLog"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Minus the sum of tr((finiteSection N z)^(2*(k+1)))/(k+1). The powers use the matrix cut off before multiplication; the length-series majorant is independent of N."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-determinant-identity"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.finite_determinant_identity"),
                H("finite_determinant_identity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural cutoff N and complex norm(z)<1, the determinant of 1-(finiteSection N z)^2 equals exp(finiteLog N z). This includes the empty determinant and arbitrary complex phases; Hermitian diagonalization is used only on the real slice."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-determinants-tendsto"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.finite_determinants_tendsto"),
                H("finite_determinants_tendsto"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At every complex point of the open unit disk, det(1-(finiteSection N z)^2) tends to gaussianDet z as N tends to infinity. This is pointwise spatial cutoff convergence, with no period identity or physical realization premise."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-log-det-differentiable-on"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.gaussianLogDet_differentiableOn"),
                H("gaussianLogDet_differentiableOn"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complex differentiability of the actual infinite signed-cycle logarithm gaussianLogDet on the full open unit disk. Summable majorants on each smaller disk control the internal vertices, the outer diagonal vertex, and the cycle length."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-det-differentiable-on"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.gaussianDet_differentiableOn"),
                H("gaussianDet_differentiableOn"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complex differentiability of gaussianDet on the full open unit disk, by composition of the actual infinite signed-cycle logarithm with the complex exponential. No period identity or physical realization premise is used."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("supplier-unit1geo"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.unit1Geo"),
                H("unit1Geo"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two-coordinate geometric majorant used by compact-uniform operator cutoffs."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("supplier-unit1geo-summable"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.unit1Geo_summable"),
                H("unit1Geo_summable"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The geometric coordinate majorant is summable at every nonnegative radius below one."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("supplier-unit1power-coordinate-bound"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.unit1Power_coordinate_bound"),
                H("unit1Power_coordinate_bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each coordinate of an operator power applied to a unit basis vector is bounded by the corresponding power of the operator norm."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("supplier-unit1section-power-coordinate"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.unit1Section_power_coordinate"),
                H("unit1Section_power_coordinate"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each finite matrix-power coordinate agrees with the corresponding embedded section-operator power coordinate, including power zero."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("supplier-unit1majorant-summable"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.unit1Majorant_summable"),
                H("unit1Majorant_summable"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cycle-length majorant is summable on each smaller disk."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("supplier-finitelogterm-bound"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.finiteLogTerm_bound"),
                H("finiteLogTerm_bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each literal finite logarithm term is bounded by the same cycle-length majorant independently of the section dimension."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("supplier-finitelog-tendsto"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDeterminant.finiteLog_tendsto"),
                H("finiteLog_tendsto"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual finite logarithms converge pointwise to the infinite signed-cycle logarithm on the full unit disk."))), DescribeRole.Theorem))));
}
