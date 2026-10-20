using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Fourier;

internal sealed class SinhLogIntegralDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Logarithmic cosine integrals for normalized hyperbolic sine.",
        H("The hyperbolic sine density"), Blocks(
            Describe.Lean(DescribeId.Create("sinh-density-positive"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/SinhLogIntegral.h_pos"),
                H("Positive density"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At positive scale and positive frequency the exponential denominator is strictly positive, so the density is strictly positive."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sinh-profile-positive"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/SinhLogIntegral.E_pos"),
                H("Positive normalized profile"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At positive scale the normalized hyperbolic sine is positive at every real argument, including zero. Away from zero numerator and denominator have the same sign."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sinh-density-scale-comparison"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/SinhLogIntegral.h_scale_le"),
                H("Comparison across scales"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive a and s and b at least a, define h(a,s)=1/(exp(pi s/a)-1). Then h(b,s) is at least (b/a) h(a,s). Convexity of the real exponential between zero and pi s/a gives the denominator comparison; all denominators are strictly positive."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sinh-density-levy-integrability"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/SinhLogIntegral.integrable_levyWeight"),
                H("Integrability of the weighted density"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive a, the function min(1,s squared) h(a,s)/s is integrable on the positive half-line. The estimate exp(x)-1 at least x bounds the integrand near zero by a/pi. Beyond one the density is bounded by a constant times exp(-pi s/a), which is integrable."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sinh-log-integrand-integrability"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/SinhLogIntegral.integrable_logIntegrand"),
                H("Absolute integrability of cosine deficits"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive a and every real t, (1-cos(ts)) h(a,s)/s is integrable on the positive half-line. The cosine deficit is nonnegative and bounded by (t squared plus two) times min(1,s squared). This supplies the absolute integrability needed for linear combinations of the logarithmic densities."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sinh-log-cosine-integral"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/SinhLogIntegral.log_E_eq_integral"),
                H("The logarithmic integral formula"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive a, let E(a,t)=sinh(at)/(at) away from zero and E(a,0)=1. For every real t, log E(a,t) equals twice the integral of (1-cos(ts)) h(a,s)/s over positive s. The formula includes t=0.")),
                    Paragraph(Text("The complex Euler sine product on the imaginary axis gives the product of 1+(at) squared divided by pi squared times n squared. Positivity permits taking logarithms. Fubini's theorem and the half-line integral of a complex exponential give the elementary formula log(1+t squared/b squared)=2 integral (1-cos(ts)) exp(-bs)/s for b positive. Summing these identities uses the geometric expansion of h and the integrable density bound. This is an identity of real Lebesgue integrals; it does not impose integrability of h itself at zero."))),
                DescribeRole.Theorem))));
}
