using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Fourier;

internal sealed class GaussianKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Fourier/GaussianKernel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized Gaussian kernels and their cosine averages.",
        H("Gaussian kernels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bromwich-exponent"),
                DeclarationHandle.Create(Prefix + "bromwich_exponent"),
                H("Expanding the vertical Gaussian exponent"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary real M, c, v, and t, the vertical Gaussian exponent expands into its quadratic, linear, and constant terms in t."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q-laws"),
                DeclarationHandle.Create(Prefix + "q_laws"),
                H("Gaussian probability densities"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive M, q(M,v)=M exp(-M²v²/2)/sqrt(2 pi) is nonnegative and integrable on the real line, with integral one. Scaling the Gaussian integral supplies the normalization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q-bromwich-integrable"),
                DeclarationHandle.Create(Prefix + "q_bromwich_integrable"),
                H("Absolute convergence on vertical lines"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive M and arbitrary real c and v, the exponential of (c+it)v+(c+it)²/(2M²) is integrable as a function of t. Its exponent is a quadratic polynomial with negative real leading coefficient."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q-bromwich"),
                DeclarationHandle.Create(Prefix + "q_bromwich"),
                H("Gaussian inversion on vertical lines"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive M, q(M,v) equals one divided by 2 pi times the integral over real t of exp((c+it)v+(c+it)²/(2M²)), for every real c. Completing the square evaluates the integral and cancels the dependence on c."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q-cos-convolution"),
                DeclarationHandle.Create(Prefix + "q_cos_convolution"),
                H("Gaussian convolution of a cosine"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The convolution of cos(gamma u) with q(M,y-u) is exp(-gamma²/(2M²)) cos(gamma y). Translation and the cosine subtraction identity reduce the formula to the cosine and sine transforms."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-halfline-correction"),
                DeclarationHandle.Create(Prefix + "gaussian_halfline_correction"),
                H("The half-line correction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For M and y at least one and positive gamma, the absolute integral over v at least zero of cos(gamma v)q(M,y+v) is at most 2M²yq(M,y)/gamma². Integrating twice by parts leaves a cosine average of the second derivative. That derivative is nonnegative on this half-line and has total mass M²yq(M,y); the Gaussian and its first derivative vanish at infinity."))),
                DescribeRole.Theorem))));
}
