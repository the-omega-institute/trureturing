using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.WallisRemainder;

internal sealed class MeasureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An odd spectral mixture and its size-biased probability law.",
        H("Spectral probability laws"), Blocks(
            Entry("wallis-tanh-fractions", "tanh_div_hasSum", "Hyperbolic partial fractions",
                "For positive u, tanh(u)/u is the sum, over natural n, of 8/(pi squared times (2n+1) squared plus 4u squared). The cotangent expansion on the positive imaginary axis gives the hyperbolic cotangent expansion. Splitting its even and odd terms gives the formula."),
            Entry("wallis-hasSum-spectralWeight", "hasSum_spectralWeight", "Spectral normalization",
                "The positive weights 8/(pi squared times (2n+1) squared), for natural n, sum to one."),
            Entry("wallis-P-pos", "P_pos", "Positive support of the spectral law",
                "The law P is the mixture, with the normalized odd spectral weights, of a(n)U squared, where U has density exp(-u) on the positive ray and a(n)=1/(4 pi squared times (2n+1) squared). It assigns full measure to strictly positive values."),
            Entry("wallis-integrable-P-id", "integrable_P_id", "Finite first moment",
                "The identity function is integrable with respect to P."),
            Entry("wallis-integrable-P-sq", "integrable_P_sq", "Finite second moment",
                "The square function is integrable with respect to P."),
            Entry("wallis-integrable-P-cube", "integrable_P_cube", "Finite third moment",
                "The cube function is integrable with respect to P."),
            Entry("wallis-integral-P-id", "integral_P_id", "The first spectral moment",
                "The mean of P is 1/24."),
            Entry("wallis-integral-P-sq", "integral_P_sq", "The second spectral moment",
                "The second moment of P is 1/80."),
            Entry("wallis-integral-P-cube", "integral_P_cube", "The third spectral moment",
                "The third moment of P is 17/1792. Gamma integrals evaluate each exponential component; the odd sums of reciprocal even powers give the exact mixture moments."),
            Entry("wallis-Q-pos", "Q_pos", "Positive support after size biasing",
                "The probability law Q, with density 24v relative to P, assigns full measure to strictly positive values."),
            Entry("wallis-integral-Q", "integral_Q", "Integration after size biasing",
                "For every real function f on the real line, its integral under Q equals 24 times the integral of v times f(v) under P."),
            Entry("wallis-integrable-Q-id", "integrable_Q_id", "Finite size-biased first moment",
                "The identity function is integrable with respect to Q."),
            Entry("wallis-integrable-Q-sq", "integrable_Q_sq", "Finite size-biased second moment",
                "The square function is integrable with respect to Q."),
            Entry("wallis-integral-Q-id", "integral_Q_id", "The size-biased mean",
                "The mean of Q is 3/10."),
            Entry("wallis-integral-Q-sq", "integral_Q_sq", "The size-biased second moment",
                "The second moment of Q is 51/224."),
            Entry("wallis-variance-P", "variance_P", "The spectral variance",
                "The variance of the identity function under P is 31/2880."),
            Entry("wallis-variance-Q", "variance_Q", "The size-biased variance",
                "The variance of the identity function under Q is 771/5600.")))));

    private static DocumentBlock Entry(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/WallisRemainder/Measure." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
