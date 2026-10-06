using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MotzkinHankel;

internal sealed class CiglerMotzkinColumnDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumnDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2022motzkin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform horizontal weights define the Hankel series of every Motzkin-triangle column and Cigler's specified denominator.",
        H("Motzkin-Column Hankel Series"),
        Blocks(
            Node("cigler-motzkin-column-defs-specialize", "Uniform horizontal weights", "specialize",
                "The integer algebra homomorphism from the polynomial ring in t and s to the integer polynomial ring in t sends both indeterminates to t. Thus every horizontal step has weight t, including steps on the axis.", DescribeRole.Definition),
            Node("cigler-motzkin-column-defs-hankel", "Column Hankel determinants", "columnHankel",
                "For nonnegative integers k, m and n, d_m^{(k)}(n,t) is the determinant of the n by n matrix with entry M_{m+i+j,k}(t) in row i and column j, for indices from zero to n minus one. Here M_{r,k}(t) sums the weights of Motzkin paths from (0,0) to (r,k) never below the axis, with up and down steps of weight one and horizontal steps of weight t. The empty determinant is one.", DescribeRole.Definition),
            Node("cigler-motzkin-column-defs-factor", "Signed Lucas factors", "columnFactor",
                "Put e = (-1)^binom(k+1,2). As polynomials in x over the integer polynomial ring in t, A_{k,0}(x,t) = 1 - e x^(k+1), and A_{k,r}(x,t) = 1 - e L_r(t)x^(k+1) + x^(2(k+1)) for positive r. The Lucas polynomials satisfy L_0 = 2, L_1 = t and L_{r+2} = t L_{r+1} - L_r. These are the factors in equation (1.28) of Cigler's paper.", DescribeRole.Definition),
            Node("cigler-motzkin-column-defs-denominator", "The specified common denominator", "columnDenominator",
                "For nonnegative integers k and m, Q_m^{(k)}(x,t) is the product of A_{k,(k+1)(m-2j)}(x,t) raised to the exponent 1 + j(m-j), over j from zero through the integer part of m divided by two.", DescribeRole.Definition),
            Node("cigler-motzkin-column-defs-claim", "Cigler's column identity", "claim",
                "For every nonnegative integer k and every integer m at least one, there is an integer polynomial R_m^{(k)}(x,t) such that R_m^{(k)} equals Q_m^{(k)} times the formal series summing d_m^{(k)}(n,t)x^n over all nonnegative n. Its degree in x is exactly binom(m+1,3) + k(binom(m,1) + binom(m,2) + binom(m,3)). This is Conjecture 1.3, equation (1.30), of Cigler's paper. The degree is over the integer polynomial ring in t; specializing t can lower it. The identity does not assert that numerator and denominator are relatively prime.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
