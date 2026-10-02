using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.PrimeNumberTheorem;

internal sealed class PntTailDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Weil/primenumbertheoremand2026medium");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The smoothed Chebyshev contour has controlled vertical and horizontal tails.",
        H("PntTail"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("i1-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/PrimeNumberTheorem/PntTail.I1Bound"),
                H("I1Bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For a nonnegative once continuously differentiable kernel supported in [1/2, 2] with unit multiplicative Haar mass, one positive constant bounds the first vertical tail by C times X times log X divided by epsilon times T, whenever X and T are greater than three and epsilon lies strictly between zero and one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("i2-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/PrimeNumberTheorem/PntTail.I2Bound"),
                H("I2Bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Let the kernel be once continuously differentiable and supported in [1/2, 2]. Assume 0 < A <= 1/2 and C2 > 0, and for every real sigma and t with |t| > 3 and sigma >= 1 - A/(log |t|)^9 assume |zeta'(sigma + it)/zeta(sigma + it)| <= C2 (log |t|)^9. Then one C > 0 bounds the norm of I2 by C X/(epsilon T) for all X > 3, T > 3 and 0 < epsilon < 1, with sigma1 = 1 - A/(log T)^9."))),
                DescribeRole.Theorem),
            Paragraph(Text("I1. Writing G(z) for the smoothed Chebyshev integrand with kernel SmoothingF and parameters epsilon, X, I1 is i/(2 pi i) times the integral of G(1 + 1/log X + it) over t <= -T.")),
            Paragraph(Text("I2. Writing G(z) for the smoothed Chebyshev integrand with kernel SmoothingF and parameters epsilon, X, I2 is 1/(2 pi i) times the oriented integral of G(sigma - iT) from sigma1 to 1 + 1/log X.")),
            Paragraph(Text("I37. Writing G(z) for the smoothed Chebyshev integrand with kernel SmoothingF and parameters epsilon, X, I37 is i/(2 pi i) times the oriented integral of G(sigma1 + it) from t = -T to t = T.")),
            Paragraph(Text("I8. Writing G(z) for the smoothed Chebyshev integrand with kernel SmoothingF and parameters epsilon, X, I8 is 1/(2 pi i) times the oriented integral of G(sigma + iT) from sigma1 to 1 + 1/log X.")),
            Paragraph(Text("I9. Writing G(z) for the smoothed Chebyshev integrand with kernel SmoothingF and parameters epsilon, X, I9 is i/(2 pi i) times the integral of G(1 + 1/log X + it) over t >= T.")),
            Paragraph(Text("I3. Writing G(z) for the smoothed Chebyshev integrand with kernel SmoothingF and parameters epsilon, X, I3 is i/(2 pi i) times the oriented integral of G(sigma1 + it) from t = -T to t = -3.")),
            Paragraph(Text("I7. Writing G(z) for the smoothed Chebyshev integrand with kernel SmoothingF and parameters epsilon, X, I7 is i/(2 pi i) times the oriented integral of G(sigma1 + it) from t = 3 to t = T.")),
            Paragraph(Text("I4. Writing G(z) for the smoothed Chebyshev integrand with kernel SmoothingF and parameters epsilon, X, I4 is 1/(2 pi i) times the oriented integral of G(sigma - 3i) from sigma2 to sigma1.")),
            Paragraph(Text("I6. Writing G(z) for the smoothed Chebyshev integrand with kernel SmoothingF and parameters epsilon, X, I6 is 1/(2 pi i) times the oriented integral of G(sigma + 3i) from sigma2 to sigma1.")),
            Paragraph(Text("I5. Writing G(z) for the smoothed Chebyshev integrand with kernel SmoothingF and parameters epsilon, X, I5 is i/(2 pi i) times the oriented integral of G(sigma2 + it) from t = -3 to t = 3.")),
            Describe.Lean(
                DescribeId.Create("log-deriv-zeta-has-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/PrimeNumberTheorem/PntTail.LogDerivZetaHasBound"),
                H("LogDerivZetaHasBound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every real sigma and t with |t| > 3 and sigma >= 1 - A/(log |t|)^9, the predicate requires |zeta'(sigma + it)/zeta(sigma + it)| <= C (log |t|)^9. The real coordinate sigma has no upper bound."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("log-deriv-zeta-is-holo-small"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/PrimeNumberTheorem/PntTail.LogDerivZetaIsHoloSmall"),
                H("LogDerivZetaIsHoloSmall"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("The predicate requires the zeta logarithmic derivative to be holomorphic on the small punctured rectangle with imaginary coordinate between minus three and three."))),
                DescribeRole.Definition))));
}
