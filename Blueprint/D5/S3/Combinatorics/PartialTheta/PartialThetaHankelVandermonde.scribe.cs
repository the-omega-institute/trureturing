using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PartialTheta;

internal sealed class PartialThetaHankelVandermondeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PartialTheta/PartialThetaHankelVandermonde.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2024partialtheta");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Vandermonde product evaluates the unshifted Hankel determinant and establishes its nonvanishing.",
        H("The Unshifted Partial Theta Hankel Determinant"),
        Blocks(
            Node("partial-theta-hankel-vandermonde-unshifted", "The unshifted determinant formula", "unshifted",
                "For every nonnegative integer n, put V_n(q) = product over d from one through n of (q^d - 1)^{n + 1 - d}. Then D_{0,n+1}(q) = q^{(n + 1) binom(n, 2)} V_n(q), and this determinant is nonzero. The polynomial V_n is monic, has degree binom(n + 2, 3), and satisfies V_n(0) = (-1)^{binom(n + 1, 2)}. Empty products are one. Extracting the row and column monomials leaves the Vandermonde matrix at 1, q, through q^n; grouping its factors by the difference of the two indices gives the displayed product.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
