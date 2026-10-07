using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MotzkinHankel;

internal sealed class CiglerMotzkinHankelNegativeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelNegative.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2022motzkin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Backward orthogonal polynomials determine the vanishing interval and first nonzero determinant at negative indices.",
        H("Negative-Index Motzkin Determinants"),
        Blocks(
            Node("cigler-motzkin-hankel-negative-backward", "Backward orthogonal polynomials", "backward",
                "The polynomials b_r(y) over the integer polynomial ring in t and s satisfy b_0 = s - t, b_1 = (y - t)b_0 - 1 and b_{r+2} = (y - t)b_{r+1} - b_r for every nonnegative integer r. They continue the orthogonal recurrence with b_r corresponding to p_{-r-1}.", DescribeRole.Definition),
            Node("cigler-motzkin-hankel-negative-determinants", "Vanishing and the first nonzero backward determinant", "negative_determinants",
                "For every nonnegative integer m and every integer a with 1 at most a and a less than m, the m by m coefficient determinant with row polynomial b_{a-1-i} when i is less than a and p_{i-a} otherwise is zero. Its column j consists of coefficients of y^j. At a = m, (-1)^m times the determinant with row polynomial b_{m-1-i} equals (-1)^binom(m+1,2) times (s - t)^m, and this polynomial is nonzero in the integer polynomial ring in t and s. This nonvanishing concerns independent indeterminates; specialization to s = t can make it zero when m is positive.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
