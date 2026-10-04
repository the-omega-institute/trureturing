using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MotzkinHankel;

internal sealed class CiglerMotzkinHankelOrthogonalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelOrthogonal.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2022motzkin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Monic orthogonal polynomials convert shifted Motzkin Hankel determinants to coefficient determinants of fixed size.",
        H("The Motzkin Orthogonal Polynomial Basis"),
        Blocks(
            Node("cigler-motzkin-hankel-orthogonal-polynomials", "The orthogonal polynomial recurrence", "orthogonal",
                "Over the integer polynomial ring in t and s, the polynomials p_r(y) are defined by p_0 = 1, p_1 = y - s and p_{r+2} = (y - t)p_{r+1} - p_r for every nonnegative integer r. The variable y is distinct from the parameters t and s.", DescribeRole.Definition),
            Node("cigler-motzkin-hankel-orthogonal-basis", "The monic basis expansion", "orthogonal_basis",
                "For every nonnegative integer n, p_n is monic of degree n, and y^n is the sum of M_{n,k}(t,s)p_k(y) over k from zero through n. Thus the Motzkin array gives the change of basis from these polynomials to monomials.", DescribeRole.Theorem),
            Node("cigler-motzkin-hankel-orthogonal-coefficients", "The coefficient determinant formula", "hankelDet_coefficients",
                "For all nonnegative integers m and n, d_m(n,t,s) equals (-1)^(mn) times the determinant of the m by m matrix whose row i and column j entry is the coefficient of y^j in p_{n+i}(y), with both indices ranging from zero to m minus one. The matrix size is the shift m, independently of the Hankel matrix size n.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
