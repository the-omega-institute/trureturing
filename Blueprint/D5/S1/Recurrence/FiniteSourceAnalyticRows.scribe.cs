using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class FiniteSourceAnalyticRowsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/FiniteSourceAnalyticRows.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite boundary sequences give rational functions whose Taylor coefficients are "
            + "the actual recursive array entries. A critical amplitude bound gives a larger "
            + "zero-free disk and a Cauchy coefficient estimate.",
        H("Analytic Rows of Finite Boundary Sequences"),
        Blocks(
            Paragraph(Text(
                "Let K be a complete nontrivially normed field of characteristic zero, "
                    + "and let b be a sequence in K with b(i) = 0 for i > M. "
                    + "The recursive array has first column b and successor equation "
                    + "T(n, k + 1) = T(n + 1, k) - sum over 0 <= j <= k of "
                    + "T(n, j) b(k - j). The finite support condition is on the boundary; "
                    + "the rows can have infinitely many nonzero coefficients.")),
            Node("finiteSource", "The finite source polynomial",
                "The polynomial F(z) = 1 + z times the sum over 0 <= i <= M of "
                    + "b(i) z^i has F(0) = 1. In particular its inverse is analytic "
                    + "on a neighborhood of zero.",
                DescribeRole.Definition),
            Node("finiteTail", "The shifted boundary polynomial",
                "For each row n, C(n, z) is the sum over 0 <= j <= M of "
                    + "b(n + j) z^j. Terms outside the boundary support vanish, "
                    + "so this is the full shifted boundary polynomial, including when n > M.",
                DescribeRole.Definition),
            Node("rationalRow", "The rational row",
                "The row function is r(n, z) = F(z)^(-1) C(n, z / F(z)). "
                    + "Its values near zero are well defined by ordinary field inversion "
                    + "because F is nonzero there. The analytic identities concern "
                    + "this neighborhood and do not cancel a denominator at its zeros.",
                DescribeRole.Definition),
            Node("result", "The actual Taylor coefficients",
                "For every row n and every degree k, the kth derivative of r(n, z) "
                    + "at zero divided by k! equals array(b, n, k). Moreover the "
                    + "scalar power series with exactly these array entries represents "
                    + "r(n, z) on a neighborhood of zero. This holds over both the "
                    + "real and complex numbers without an amplitude hypothesis. "
                    + "To prove it, finite support gives C(n, w) = b(n) + w C(n + 1, w). "
                    + "On a zero-free neighborhood this becomes F(z) r(n, z) = "
                    + "b(n) + z r(n + 1, z). The absolutely convergent Cauchy product "
                    + "identifies the coefficients of this analytic identity. They obey "
                    + "the stated boundary and successor equations, so uniqueness of "
                    + "the recursive array identifies all coefficients simultaneously.",
                DescribeRole.Theorem),
            Node("critical_radius", "An enlarged disk and Cauchy's estimate",
                "For complex b suppose A > 0, 0 < rho < 1, "
                    + "A rho = (1 - rho)^2, and the norm of every b(i) is at most A. "
                    + "There is a radius R with rho < R < 1 such that the norm of F(z) "
                    + "is strictly greater than rho throughout the closed disk of radius R. "
                    + "Every rational row is represented on the open R disk by the "
                    + "power series of its actual recursive coefficients. For every n and k, "
                    + "the norm of array(b, n, k) is at most the circular average of "
                    + "the norm of r(n, z) on the R circle, multiplied by R^(-k). "
                    + "Indeed, the scalar majorant Q(t) = A t times the sum over "
                    + "0 <= i <= M of t^i satisfies "
                    + "Q(rho) = (1 - rho)(1 - rho^(M + 1)) < 1 - rho. "
                    + "Continuity preserves this strict inequality at a larger R < 1. "
                    + "The triangle inequality then gives the lower bound for F on "
                    + "the closed disk. The Cauchy expansion and the Taylor germ "
                    + "represent the same function, so uniqueness identifies their "
                    + "coefficients. The multilinear coefficient norm equals the "
                    + "scalar coefficient norm, giving the displayed estimate. "
                    + "The radius depends on the amplitude, the critical weight, and "
                    + "the finite support bound; no radius uniform in all support bounds is asserted.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create("finite-source-analytic-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))),
            role);
}
