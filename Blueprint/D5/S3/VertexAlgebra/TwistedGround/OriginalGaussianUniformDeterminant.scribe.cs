using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianUniformDeterminantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original Gaussian Uniform Trace Logarithms and Determinants",
        H("Original Gaussian Uniform Trace Logarithms and Determinants"),
        Blocks(
            Paragraph(Text("For every nonnegative radius strictly below one, the original finite Gaussian trace logarithms converge uniformly on the closed complex disk. Each trace is expanded as the sum of an original signed matrix entry times a coordinate of a power of the actual cutoff operator. The geometric entry majorant controls the spatial tails, while the summable trace-length majorant controls the logarithm series. Uniform operator convergence and a telescoping power estimate control the remaining terms. The pointwise trace-log limit identifies the uniform limit.")),
            Paragraph(Text("All finite logarithms and their limit lie in one bounded closed complex ball. Continuity of the exponential on this compact ball therefore preserves uniform convergence. The finite determinant identity and the complex period identity give the literal finite determinants converging to the product of the principal-branch exponential and the existing half-binomial period. The finite matrix is squared after cutoff, including the empty section. Radius zero is included.")),
            Paragraph(Text("This supplies uniform analytic control for the original Gaussian coefficient model. Original energy-source factorization, its coefficient identity, and the full Moonshine, vertex operator algebra, conformal field theory, string theory and AdS/CFT construction require further results.")),
            Describe.Lean(
                DescribeId.Create("finite-log-tendsto-uniformly-on"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformDeterminant.finiteLog_tendstoUniformlyOn"),
                H("finiteLog_tendstoUniformlyOn"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual finite trace logarithms converge to gaussianLogDet uniformly on every closed disk of nonnegative radius less than one."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-determinants-tendsto-uniformly-on-period"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianUniformDeterminant.finite_determinants_tendstoUniformlyOn_period"),
                H("finite_determinants_tendstoUniformlyOn_period"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Determinants of one minus the square of each original finite section converge uniformly on the same disk to exp((1/4) log(1-z squared)) times period(z squared). The period occurs as a product factor."))), DescribeRole.Theorem))));
}
