using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class OriginalHalfBinomialIntegralDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal original half-binomial-square series equals its normalized elliptic sine integral.",
        H("Original Half-Binomial Elliptic Integral"),
        Blocks(Describe.Lean(
            DescribeId.Create("original-half-binomial-elliptic-integral"),
            DeclarationHandle.Create("D5/S3/Analytic/OriginalHalfBinomialIntegral.original_series_eq_integral"),
            H("Summability, integrability and the exact identity including zero"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every real r with 0<=r<1, the complex series with nth term "
                    + "halfBinomial(n)^2 times (r:Complex)^n is summable. The real function "
                    + "theta maps to 1/sqrt(1-r*sin(theta)^2) is interval integrable from zero "
                    + "to pi/2, and the sum of that same complex series equals the complex "
                    + "embedding of (2/pi) times that real integral. The original coefficient "
                    + "halfBinomial(n) is the product of (-1/2-j) for 0<=j<n, divided by n!, "
                    + "including its zeroth term and its alternating sign before squaring. No analytic identity or "
                    + "convergence assertion is a hypothesis.")),
                Paragraph(Text("Write b_n=centralBinom(n)/4^n. The original successor law gives "
                    + "halfBinomial(n)=(-1)^n b_n. Mathlib's binomial power series identifies "
                    + "sum b_n u^n with 1/sqrt(1-u) for 0<=u<1. The sine-power reduction "
                    + "formula gives integral from zero to pi/2 of sin(theta)^(2n) equal "
                    + "to (pi/2)b_n. Each term b_n r^n sin(theta)^(2n) is bounded in "
                    + "absolute value by r^n, since 0<=b_n<=1 and sin(theta)^2<=1. "
                    + "The summable geometric bound justifies termwise interval integration. "
                    + "Continuity and the lower bound 1-r>0 give actual integrability of "
                    + "the square-root kernel. Uniqueness of sums and the real-to-complex "
                    + "continuous embedding yield the displayed literal identity.")),
                Paragraph(Text("This is the classical Euler-Gauss representation of the "
                    + "complete elliptic integral, with parameter r and normalization 2/pi. "
                    + "No originality claim is made. The result supplies the analytic bridge "
                    + "needed for complementary-period endpoint estimates; it does not "
                    + "establish the logarithmic constant, the nome, an original Gaussian "
                    + "realization, crossing, string theory or an AdS/CFT correspondence."))),
            DescribeRole.Theorem))));
}
