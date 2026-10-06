using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PartialTheta;

internal sealed class PartialThetaHankelHighestDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PartialTheta/PartialThetaHankelHighest.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2024partialtheta");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The extremal determinant terms determine the degree, leading coefficient, and constant coefficient of every normalized quotient.",
        H("The Extremal Coefficients of the Hankel Quotient"),
        Blocks(
            Node("partial-theta-hankel-highest-quotient-data", "Degree and extremal coefficients", "quotient_data",
                "For all nonnegative integers m and n and every polynomial r(q) with integer coefficients satisfying D_{-m,n+m+1}(q) = (-1)^{binom(m + 1, 2)} r(q) q^{m binom(n, 2)} D_{0,n+1}(q), the polynomial r is monic, has degree mn(n + m + 2)/2, and satisfies r(0) = (-1)^{mn}. The unique maximal-degree determinant term comes from the permutation that reverses the indices zero through m and fixes the remaining indices. Its coefficient and degree, compared with those of the normalizing factors, give the leading coefficient and degree of r. The lowest nonzero determinant coefficient gives its constant coefficient.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
