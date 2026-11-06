using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace;

internal sealed class QuantitativeFejerBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Laplace/QuantitativeFejerBoundary.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A one-sided logarithmic envelope gives absolute Laplace convergence and a uniform quantitative Fejer boundary formula.",
        H("Laplace convergence from a logarithmic envelope"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("laplace-converges-of-log-envelope"),
                DeclarationHandle.Create(Prefix + "laplace_converges_of_log_envelope"),
                H("Absolute convergence on the positive real ray"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let a locally finite positive spectrum have positive integral multiplicities "
                    + "and counting function asymptotic to T log(T)/(2 pi). Suppose a measurable, "
                    + "locally bounded real function has an absolutely convergent Laplace transform "
                    + "for real parts greater than one half, agreeing between one half and one "
                    + "with minus one half of the paired pole sum plus a holomorphic remainder. "
                    + "Assume that either the function or its negative is bounded above on the "
                    + "nonnegative real axis by kappa log(exp(1)+u)+C, for nonnegative kappa and C. "
                    + "Then the absolute Laplace integral converges at every positive real parameter. "
                    + "An affine majorant of the logarithmic envelope gives a nonnegative difference. "
                    + "The paired inverse-square tail estimate continues its transform along the "
                    + "positive real axis. Landau's singularity theorem excludes a positive "
                    + "convergence boundary; subtracting the majorant recovers absolute convergence "
                    + "of the original function."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quantitative-boundary-formula"),
                DeclarationHandle.Create(Prefix + "quantitative_boundary_formula"),
                H("The quantitative Fejer boundary formula"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the same spectral and Laplace hypotheses, there is a positive constant "
                    + "depending only on the given spectrum and Laplace data. For every Fejer kernel "
                    + "or notched Fejer kernel of positive bandwidth b whose Fourier transform is "
                    + "supported in the interval from minus M to M, with M at least four and y at "
                    + "least one, the convolution of f with the kernel over the nonnegative ray is "
                    + "absolutely integrable whenever f has a one-sided logarithmic envelope. Its "
                    + "difference from minus the finite cosine sum over ordinates at most twice M, "
                    + "weighted by their multiplicities and the kernel's Fourier transform, is "
                    + "bounded by that constant times the sum of (1+b) times M to the maximum of "
                    + "k and one, divided by y, and N(2M) divided by the product of b and y. The constant is uniform in "
                    + "the kernel, b, M, y, and the logarithmic envelope. The proof first continues "
                    + "the transform throughout the positive strip and applies absolute Fubini "
                    + "with exponential damping. Monotone convergence of the nonnegative "
                    + "difference between the envelope and the signed function establishes "
                    + "integrability before damping is removed. The negative-ray kernel tail "
                    + "bounds the truncation error, and integration by parts on the linear pieces "
                    + "of the Fourier weight bounds the regular part."))),
                DescribeRole.Theorem))));
}
