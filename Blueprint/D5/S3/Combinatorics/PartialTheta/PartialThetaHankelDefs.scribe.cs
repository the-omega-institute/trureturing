using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PartialTheta;

internal sealed class PartialThetaHankelDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PartialTheta/PartialThetaHankelDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2024partialtheta");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Backward shifts of partial theta coefficients define Hankel determinants and their normalized polynomial quotients.",
        H("Partial Theta Coefficients and Hankel Determinants"),
        Blocks(
            Node("partial-theta-hankel-defs-coeff-a", "The partial theta coefficient", "coeffA",
                "For every integer s, a(s, q) is q^{binom(s, 2)} when s is nonnegative and zero when s is negative. It is a polynomial in q with integer coefficients. These are the coefficients of the partial theta series summed over nonnegative s of q^{binom(s, 2)} x^s, extended by zero to negative indices.", DescribeRole.Definition),
            Node("partial-theta-hankel-defs-hankel", "The backward-shifted Hankel determinant", "hankel",
                "For nonnegative integers m and N, D_{-m,N}(q) is the determinant of the N by N matrix with entry a(-m + i + j, q) in row i and column j, where i and j range from zero through N - 1. The determinant is a polynomial in q with integer coefficients; the determinant of the empty matrix is one.", DescribeRole.Definition),
            Node("partial-theta-hankel-defs-claim", "The normalized quotient conjecture", "claim",
                "For every pair of nonnegative integers m and n, D_{0,n+1}(q) is nonzero and there exists a polynomial r_{m,n}(q) with integer coefficients such that D_{-m,n+m+1}(q) = (-1)^{binom(m + 1, 2)} r_{m,n}(q) q^{m binom(n, 2)} D_{0,n+1}(q). This polynomial is monic, has degree mn(n + m + 2)/2, and satisfies r_{m,n}(1) = 1 and r_{m,n}(0) = (-1)^{mn}. This is the conjecture following equation (2) in Section 1 of Cigler's paper, together with nonvanishing of the unshifted determinant.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
