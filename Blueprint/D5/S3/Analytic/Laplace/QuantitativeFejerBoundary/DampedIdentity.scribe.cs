using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace.QuantitativeFejerBoundary;

internal sealed class DampedIdentityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Laplace/QuantitativeFejerBoundary/DampedIdentity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourier inversion and damping limits control convolutions with admissible Fejer kernels.",
        H("Damped convolution identities"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("admissible-laws"),
                DeclarationHandle.Create(Prefix + "admissible_laws"),
                H("Continuity, positivity and Fourier support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive bandwidth, an admissible kernel and its weight are continuous and integrable, the kernel is nonnegative, its angular Fourier transform equals the weight, and the weight vanishes outside the prescribed interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("damped-fubini"),
                DeclarationHandle.Create(Prefix + "damped_fubini"),
                H("Fourier inversion for a damped convolution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let g be continuous and integrable, with integrable angular Fourier transform w. If q(u)*exp(-sigma*u) is integrable on the nonnegative ray, the damped convolution with g equals one over two pi times the integral of w(t), the Laplace transform at sigma+i*t, and exp(i*t*y)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pole-polynomial"),
                DeclarationHandle.Create(Prefix + "polePolynomial"),
                H("The finite spectral cosine polynomial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The spectral pole polynomial at M is minus the sum of multiplicity times cos(gamma*u) over positive ordinates at most twice M."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("pole-polynomial-continuous"),
                DeclarationHandle.Create(Prefix + "polePolynomial_continuous"),
                H("Continuity of the spectral polynomial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every finite spectral cosine polynomial is continuous on the real line."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pole-polynomial-convergence"),
                DeclarationHandle.Create(Prefix + "polePolynomial_convergence"),
                H("Absolute Laplace convergence of the spectral polynomial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite spectral cosine polynomial multiplied by exp(-sigma*u) is integrable on the nonnegative ray for every positive sigma."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pole-polynomial-laplace"),
                DeclarationHandle.Create(Prefix + "polePolynomial_laplace"),
                H("The Laplace transform of the spectral polynomial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At every complex s with positive real part, the Laplace transform of the finite spectral cosine polynomial is minus one half of the paired pole sum over ordinates at most twice M."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("damping"),
                DeclarationHandle.Create(Prefix + "damping"),
                H("A sequence of damping parameters"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The nth damping parameter is one over twice the quantity n+1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("damping-pos"),
                DeclarationHandle.Create(Prefix + "damping_pos"),
                H("Positive damping parameters"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every term of the damping sequence is strictly positive."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("damping-lt-one"),
                DeclarationHandle.Create(Prefix + "damping_lt_one"),
                H("Damping parameters below one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every term of the damping sequence is strictly less than one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("damped-integral-tendsto"),
                DeclarationHandle.Create(Prefix + "damped_integral_tendsto"),
                H("Removal of damping from an integrable function"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a real function integrable on the nonnegative ray, the integrals after multiplication by exp(-damping(n)*u) converge to its original integral."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("admissible-log-integrable"),
                DeclarationHandle.Create(Prefix + "admissible_log_integrable"),
                H("Integrable logarithmic kernel averages"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an admissible kernel of positive bandwidth and y at least one, the function g(y-u)*log(exp(1)+u) is integrable over the nonnegative ray."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("regular-integral-tendsto"),
                DeclarationHandle.Create(Prefix + "regular_integral_tendsto"),
                H("Boundary convergence of the regular part"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For logarithmic spectral counting asymptotics, paired Laplace data, continuous w and M at least one, the integrals over [-M,M] of w(t) times the regular part at damping(n)+i*t times exp(i*t*y) converge to the corresponding boundary integral at i*t."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("admissible-bounded"),
                DeclarationHandle.Create(Prefix + "admissible_bounded"),
                H("A uniform pointwise bound for the kernels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every admissible kernel of positive bandwidth b has absolute value at most b divided by pi at every real argument."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pole-polynomial-bound"),
                DeclarationHandle.Create(Prefix + "polePolynomial_bound"),
                H("Bounding the polynomial by spectral mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The absolute value of the finite spectral cosine polynomial at every real argument is at most the spectral counting mass at twice M."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("damped-cast-integral"),
                DeclarationHandle.Create(Prefix + "damped_cast_integral"),
                H("Real and complex forms of a damped integral"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real q and g, the complex integral of q(u)*exp(-sigma*u)*g(y-u) over the nonnegative ray equals the complex embedding of the corresponding real integral."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integrable-of-one-sided-damping"),
                DeclarationHandle.Create(Prefix + "integrable_of_one_sided_damping"),
                H("Integrability from a one-sided majorant and damping limits"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let q and a be measurable on the real line, with a integrable on the nonnegative ray, and let e have absolute value one. If e*q is bounded above by a on that ray, all damped versions of q are integrable there, and their integrals converge to a finite real limit, then q is integrable there."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pole-polynomial-truncation-error"),
                DeclarationHandle.Create(Prefix + "polePolynomial_truncation_error"),
                H("The negative-ray truncation error"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an admissible kernel of positive bandwidth and positive y, the absolute difference between its nonnegative-ray convolution with the spectral polynomial and the full Fourier-weighted cosine sum is at most the spectral mass at twice M times four divided by pi*b*y."))),
                DescribeRole.Theorem))));
}
