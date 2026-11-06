using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Fourier;

internal sealed class ConvolutionL2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Fourier/ConvolutionL2.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Concrete convolution bounds for square-integrable functions.",
        H("Convolution in L²"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("real-convolution-identity"),
                DeclarationHandle.Create(Prefix + "real_convolution_identity"),
                H("Complexification of real convolution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Convolving the complexifications of two real functions agrees with the complexification of their real convolution integral."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("convolution-memlp-two"),
                DeclarationHandle.Create(Prefix + "convolution_memLp_two"),
                H("Young’s inequality in L²"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If q is integrable and f is square-integrable on the real line, their multiplication convolution is square-integrable and its L² norm is at most the integral of the norm of q times the L² norm of f. Weighted Cauchy–Schwarz bounds the squared integrand, and Tonelli together with translation invariance gives the norm estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("schwartz-convolution-l2-multiplier"),
                DeclarationHandle.Create(Prefix + "schwartz_convolution_l2_multiplier"),
                H("Bounded Schwartz multipliers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let k be a Schwartz kernel whose Fourier transform has norm at most the nonnegative number B everywhere. For every square-integrable complex f, the concrete convolution k*f is square-integrable and has L² norm at most B times the L² norm of f. The convolution Fourier identity and Schwartz Plancherel give the bound on Schwartz inputs. Schwartz density, the pointwise Hölder convolution bound, and Fatou extend it to every L² input."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("real-convolution-l2-young"),
                DeclarationHandle.Create(Prefix + "real_convolution_l2_young"),
                H("A real squared Young bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let k be a real integrable kernel with integral of its absolute value at most B, where B is nonnegative. For every measurable real f with integrable square, the integral of (k*f)² is at most B² times the integral of f². In particular, the input hypotheses hold for bounded measurable functions supported in a compact interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("real-schwartz-convolution-l2-multiplier-of-complex"),
                DeclarationHandle.Create(Prefix + "real_schwartz_convolution_l2_multiplier_of_complex"),
                H("Real-valued complex Schwartz kernels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Suppose a complex Schwartz kernel k is the complexification of a real function r, and its Fourier transform has norm at most a nonnegative B. For every measurable real f with integrable square, the square of r*f is integrable and its integral is at most B² times the integral of f². The complex convolution multiplier bound supplies square integrability, and taking real parts identifies the real convolution."))),
                DescribeRole.Theorem))));
}
