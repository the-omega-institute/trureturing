using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class PetzDyadicEscapeSpectrumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "In the finite diagonal Petz strip-Gram model, equal-mean rate laws can have uniformly close scale profiles while remaining separated in Wasserstein distance.",
        H("Inversion obstruction for the finite diagonal Petz profile"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("petz-dyadic-escape-rate-profile"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzDyadicEscapeSpectrum.rateProfile"),
                H("Finite diagonal rate profile"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite family of real rates rᵢ and real weights wᵢ, sum the strip Gram on the diagonal at −srᵢ with weights wᵢ and divide by the real scale s. " +
                    "For s ≠ 0 each summand is wᵢ (exp(−srᵢ) − 1 + srᵢ)/s. The profile is zero at s = 0. " +
                    "Before division, the sum equals the Laplace transform of the weighted rates minus the total weight plus s times the first rate moment."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("petz-dyadic-escape-diagonal-error"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzDyadicEscapeSpectrum.diagonal_log_ratio_profile_error"),
                H("Uniform error for diagonal logarithmic ratios"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix ε > 0, nonnegative rates rᵢ and positive weights wᵢ. The diagonal source values are εwᵢ and the reference values are exp(−rᵢ/ε). " +
                        "Assume every logarithmic ratio log(exp(−rᵢ/ε)) − log(εwᵢ) is nonpositive. " +
                        "For every real s > 0, evaluate each diagonal strip Gram at sε times that ratio, sum with weights wᵢ and divide by s. " +
                        "The absolute error relative to the finite rate profile is at most ε times the sum of wᵢ |log(εwᵢ)| over the finite index set.")),
                    Paragraph(Text(
                        "The diagonal kernel exp(x) − 1 − x is one-Lipschitz on the nonpositive half-line. " +
                        "The frequency shift from −srᵢ is −sε log(εwᵢ), so division by s removes the scale from the bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("petz-dyadic-escape-profile-derivative"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzDyadicEscapeSpectrum.hasDerivAt_rateProfile"),
                H("Derivative at nonzero scales"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any finite real rates and weights and every real s ≠ 0, the derivative is the weighted sum of (1 − (1 + srᵢ) exp(−srᵢ))/s². " +
                    "Apply the quotient rule to each diagonal summand."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("petz-dyadic-escape-binomial-profile-difference"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzDyadicEscapeSpectrum.binomial_profile_difference"),
                H("Exact difference of the even and odd binomial profiles"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a natural number n > 1 and real r₀ and η, take rates r₀ + jη for j from 0 through n. " +
                        "Each law assigns weight (n choose j)/2^(n−1) on its own parity of j and zero on the other parity. " +
                        "The two laws have unit mass and equal first rate moments, so the affine terms in their profiles cancel.")),
                    Paragraph(Text(
                        "The binomial theorem gives the even profile minus the odd profile as exp(−sr₀)(1 − exp(−sη))^n / (2^(n−1) s) at every real s ≠ 0. " +
                        "At s = 0 both profiles are zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("petz-dyadic-escape-coalescing-binomial-witness"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzDyadicEscapeSpectrum.coalescing_binomial_witness"),
                H("Equal-mean coalescing laws with m atoms each"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a natural number m ≥ 2, set n = 2m − 1. If a > 0 and η > 0 satisfy a + nη ≤ b, the grid a + jη for j from 0 through n is strictly increasing in [a, b]. " +
                        "The even and odd laws on this grid are nonnegative probabilities with exactly m atoms each and the same mean.")),
                    Paragraph(Text(
                        "For every real s > 0 the absolute profile difference is at most Kη^n, where K = (n−1)! / (2^(n−1) a^(n−1)). " +
                        "The inequality 1 − exp(−sη) ≤ sη leaves the factor exp(−sa) s^(n−1), which is bounded on the positive half-line because a > 0.")),
                    Paragraph(Text(
                        "Their finite Wasserstein-1 distance is the infimum of coupling costs for absolute rate distance. " +
                        "Each coupling sends the unit mass from even to odd grid indices across a rate distance of at least η, so W₁ ≥ η."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("petz-dyadic-escape-no-uniform-holder-inverse"),
                DeclarationHandle.Create("D5/S3/Analytic/PetzDyadicEscapeSpectrum.no_uniform_holder_inverse"),
                H("Obstruction above the Hölder exponent 1/(2m − 1)"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a natural number m ≥ 2, a rate interval [a, b] with 0 < a < b, and α > 1/(2m − 1). " +
                        "There is no C ≥ 0 such that W₁ ≤ Cδ^α for every pair of probability laws on a common strictly increasing grid of 2m rates in [a, b], each with exactly m atoms and with equal means, whenever δ > 0 bounds the absolute difference of their profiles for every real s > 0.")),
                    Paragraph(Text(
                        "For any proposed C, choose the binomial pair with η small enough that C(Kη^(2m−1))^α < η. " +
                        "The same pair and tolerance δ = Kη^(2m−1) satisfy the discrepancy bound simultaneously at every positive scale, so the obstruction also holds for any choice of positive sample scales."))),
                DescribeRole.Theorem))));
}
