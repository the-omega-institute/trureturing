using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PartialTheta;

internal sealed class PartialThetaHankelQuotientDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PartialTheta/PartialThetaHankelQuotient.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2024partialtheta");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral division of an augmented alternant constructs the normalized shifted Hankel quotient.",
        H("An Integral Quotient for the Shifted Determinant"),
        Blocks(
            Node("partial-theta-hankel-quotient-integral-quotient", "Integral alternant division", "integral_quotient",
                "For nonnegative integers m and n, set N = n + m + 1. There exists r(q) in the integer polynomial ring such that D_{-m,N}(q) = (-1)^{binom(m + 1, 2)} r(q) q^{m binom(n, 2)} D_{0,n+1}(q). More precisely, form an N by N matrix A over the polynomial ring in x_0 through x_n with coefficients in the integer polynomial ring in q. For row i below m, its entry in column j is zero if j is below m - i and is q^{binom(m - i + 1, 2) + (m - i)(N - j)} otherwise. For row i at least m, its entry is x_{i-m}^j. There exists an integral polynomial B with det A = product over 0 at most u less than v at most n of (x_v - x_u), multiplied by B. Set t_i = (m - i)N for i below m and t_i = 0 otherwise. The same r and B satisfy q^{sum_i t_i + N binom(n, 2)} r(q) = (-1)^{binom(m + 1, 2)} q^{sum_j binom(j, 2) + 2 binom(n + 1, 3)} B(1, q, through q^n), where both sums range from zero through N - 1.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
