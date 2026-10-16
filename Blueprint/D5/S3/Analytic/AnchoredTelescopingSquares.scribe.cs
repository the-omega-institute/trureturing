using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class AnchoredTelescopingSquaresDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Factorization =
        LibraryNoteRef.Create("D5/L/Fourier/ephremidze2010polynomial");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every strictly positive real polynomial of positive even degree admits anchored telescoping squares.",
        H("Anchored Telescoping Squares"),
        Blocks(Describe.Lean(
            DescribeId.Create("exists-monic-lower-factor"),
            DeclarationHandle.Create(
                "D5/S3/Analytic/AnchoredTelescopingSquares.exists_monic_lower_factor"),
            H("Constructing the lower spectral factor from positivity"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Factorization),
            Blocks(
                Paragraph(Text("Let d be a real polynomial of natural degree exactly 2m, "
                    + "where m is any natural number, and suppose d(t)>0 for every real t. "
                    + "Then delta, the coefficient of degree 2m, is positive. There is a "
                    + "monic complex polynomial B of natural degree exactly m such that "
                    + "every root of B has strictly negative imaginary part and the "
                    + "complexification of d equals delta times B times its coefficient "
                    + "conjugate. No factor, root ordering, simple-root hypothesis or "
                    + "continuous choice of individual roots is assumed. Degree zero is included.")),
                Paragraph(Text("Complexify d to P. Its root multiset is invariant under "
                    + "conjugation because every coefficient is real. Positivity excludes "
                    + "real roots. Filter this multiset by negative imaginary part to obtain L. "
                    + "Conjugation maps L onto the positive-imaginary-part multiset, with "
                    + "multiplicities. These two multisets partition all roots of P, so "
                    + "each has cardinality m. Take B to be the product of X-z over L. "
                    + "The fundamental theorem of algebra gives the exact product identity. "
                    + "Evaluating at zero gives d(0)=delta times the squared complex modulus "
                    + "of B(0). Since d(0)>0 and a squared modulus is nonnegative, delta>0.")),
                Paragraph(Text("For the anchored construction, apply this factorization to "
                    + "H_s=d+s squared. Its leading coefficient is lambda=delta+s_m squared. "
                    + "The positive-leading factor is b=sqrt(lambda) B. Its value at -1 "
                    + "is nonzero, so multiplication by conjugate(b(-1))/abs(b(-1)) makes "
                    + "the anchor a(-1) positive real. The existing coefficient-continuity "
                    + "theorem applies to the monic factors of H_s/lambda, including repeated "
                    + "roots. The further anchored telescoping conclusion requires a fixed "
                    + "point of the shifted imaginary-part map; factor existence alone "
                    + "does not assert that conclusion.")),
                Paragraph(Text("This is the classical scalar polynomial spectral-factor "
                    + "construction by conjugate root pairs, using Mathlib's algebraic closure "
                    + "and multiset factorization. The scalar case of Ephremidze, An Elementary "
                    + "Proof of the Polynomial Matrix Spectral Factorization Theorem, "
                    + "arXiv:1011.3777v1, Theorem 2, supplies the corresponding classical "
                    + "spectral-factor context. No originality or algorithmic complexity "
                    + "claim is made."))),
            DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-anchored-telescoping-squares"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/AnchoredTelescopingSquares.exists_anchored_telescoping_squares"),
                H("Anchored telescoping squares in every positive even degree"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every integer m>=1 and every real polynomial d of natural "
                        + "degree exactly 2m that is strictly positive at every real input, "
                        + "there are real polynomials p,s with p of degree exactly m, s of "
                        + "degree at most m, s(0)=0, and d(t)=p(t) squared+s(t+1) squared "
                        + "-s(t) squared for every real t. The square of the coefficient "
                        + "p_m is the positive coefficient d_(2m). Repeated roots, s=0 "
                        + "and s_m=0 are all allowed. No factor or fixed point is assumed.")),
                    Paragraph(Text("Let c(j) be the sum of d(k) for 0<=k<j. Use Lagrange "
                        + "interpolation at 0,...,m to encode the cube by s(0)=0 and "
                        + "s(j)=(2x(j)-1)sqrt(c(j)). Thus s(j) squared is at most c(j). "
                        + "The polynomial H=d+s squared has degree exactly 2m because its "
                        + "top coefficient is the positive top coefficient of d plus a square. "
                        + "Its normalized lower factor is coefficientwise continuous by "
                        + "the existing lower-factor theorem. Multiply by sqrt(lambda) "
                        + "and then by conjugate(b(-1))/norm(b(-1)) to obtain a continuous "
                        + "factor with positive real value at -1. The denominator is nonzero "
                        + "by positivity of H.")),
                    Paragraph(Text("The squared imaginary part at j-1 is bounded by "
                        + "H(j-1), which is at most d(j-1)+c(j-1)=c(j). After affine "
                        + "normalization these values define a continuous cube self-map. "
                        + "Apply the existing finite-cube fixed-point theorem. The resulting "
                        + "imaginary-part identity holds at m+1 distinct points, including "
                        + "the anchor, so equality of bounded-degree polynomials extends it "
                        + "to the entire real line. Take p to be the coefficientwise real part of the factor. "
                        + "Its real evaluations and the fixed imaginary-part identity "
                        + "give the stated telescope. Translation preserves the coefficient "
                        + "of degree m of every polynomial of degree at most m, including "
                        + "polynomials of smaller degree. Hence the two shifted s-squares "
                        + "cancel at degree 2m. The remaining coefficient is p_m squared, "
                        + "which equals the positive top coefficient of d and forces the "
                        + "degree of p to be exactly m."))),
                DescribeRole.Theorem))));
}
