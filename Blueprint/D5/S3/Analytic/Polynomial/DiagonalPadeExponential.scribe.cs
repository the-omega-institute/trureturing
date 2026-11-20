using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Polynomial;

internal sealed class DiagonalPadeExponentialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Polynomial/DiagonalPadeExponential.";
    private static readonly LibraryNoteRef Scardino =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/scardino2026pade");
    private static readonly LibraryNoteRef Dlmf =
        LibraryNoteRef.Create("D5/L/Analytic/dlmf2010halfintbessel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The rational diagonal exponential Padé denominator has an exact half-integer Bessel representation "
        + "and its reciprocal coefficients are given by a sum over simple poles.",
        H("Diagonal exponential Padé denominator"),
        Blocks(
            Node("denominator", "Normalized rational denominator",
                "For natural m, the coefficient of degree j through m is "
                + "(-1)^j binom(m,j) (2m-j)!/(2m)!. Terms above m are zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Scardino)),
            Node("normalization", "Factorial normalization", "The factorial factor is m!/(2m)!.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("denominator_eq_reverse", "Reversal of the finite carrier",
                "Reverse the degree-m carrier P_m, substitute -X/2 and multiply by 2^m m!/(2m)!. "
                + "The reversal changes index j to m-j and the binomial factorial identity "
                + "converts the resulting coefficient to the diagonal denominator coefficient.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Scardino, Dlmf)),
            Node("connectionFactor", "Principal square-root factor",
                "The factor N_m(z) is m! z^m sqrt(z/pi)/(2m)!, using the principal square root.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("denominator_eq_bessel", "Exact regular and decaying carrier connection",
                "For every natural m and Re z > 0, N_m(z) is nonzero and the complex denominator "
                + "equals N_m(z) exp(-z/2) (K_m(z/2) + (-1)^m pi I_m(z/2)). "
                + "The reflected finite carrier and reversal give the sign and scale. "
                + "Positive real scaling of the principal root cancels the Bessel prefactor.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Scardino, Dlmf)),
            Node("reciprocalCoefficient", "Rational reciprocal coefficient",
                "The coefficient is extracted in the rational formal power series ring from the "
                + "inverse of the normalized denominator.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Scardino)),
            Node("hasFPowerSeriesAt_reciprocal", "Taylor coefficients of the same reciprocal",
                "After rational-to-complex casting, the formal reciprocal coefficients give "
                + "the analytic Taylor expansion at zero of the inverse of the complex denominator. "
                + "The constant coefficient is one. Multiplying the analytic Taylor expansion "
                + "by the polynomial and comparing the Cauchy product with one identifies "
                + "the formal inverse. On the right half-plane the denominator has the exact "
                + "Bessel representation above.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Scardino)),
            Node("denominator_root_derivative", "Nonzero simple roots and signed derivative",
                "For every natural m and complex root z of q_m, both z and q_m'(z) are nonzero. "
                + "The identity q_m(-z) q_m'(z) = (-1)^m (m!/(2m)!)^2 z^(2m) "
                + "follows by reversing the finite carrier, differentiating at the root, "
                + "and applying the reflected carrier Wronskian at 2/z.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Scardino)),
            Node("residueWeight", "Geometric weight of a simple pole",
                "The coefficient of the term (1 - z/ζ)^(-1) at a nonzero simple pole ζ "
                + "is R_m(ζ) = -1/(ζ q_m'(ζ)).",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Scardino)),
            Node("residueWeight_eq", "Odd-order weight with factorial normalization",
                "For every odd m and root ζ, R_m(ζ) equals "
                + "q_m(-ζ)/((m!/(2m)!)^2 ζ^(2m+1)).",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Scardino)),
            Node("reciprocalCoefficient_eq_sum", "Reciprocal coefficients as a sum over distinct roots",
                "For every positive natural m and natural n, the complex cast of the rational "
                + "reciprocal coefficient is the sum of R_m(ζ) (ζ^(-1))^n over the distinct "
                + "complex roots of q_m. Factoring over those roots and applying barycentric "
                + "Lagrange interpolation to the constant one gives the partial fractions. "
                + "Geometric expansions near zero and Taylor uniqueness identify their coefficients "
                + "with the rational formal inverse.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Scardino)),
            Node("residueWeight_pos", "Positive weight at a positive real pole",
                "For every odd m and positive real root r, R_m(r) is a positive real number. "
                + "The reflected denominator has nonnegative coefficients and constant term one.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Scardino)),
            Node("norm_normalized_residueWeight_le", "Normalized modulus bound",
                "For every odd m, natural n, positive real root r, and complex root ζ with "
                + "r ≤ |ζ|, the modulus of (R_m(ζ)/R_m(r)) (r/ζ)^n is at most "
                + "(r/|ζ|)^(n+m+1). The reflected coefficients are nonnegative and their "
                + "powers have degree at most m.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Scardino)))));

    private static DocumentBlock Node(string name, string title, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("diagonal-pade-exponential-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            provenance, Blocks(Paragraph(Text(prose))), role);
}
