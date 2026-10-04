using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MotzkinHankel;

internal sealed class CiglerMotzkinHankelDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankelDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2022motzkin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Boundary-weighted Motzkin paths determine Hankel series over the integer polynomial ring in t and s.",
        H("Boundary-Weighted Motzkin Hankel Series"),
        Blocks(
            Node("cigler-motzkin-hankel-defs-base", "The coefficient ring", "Base",
                "The coefficient ring is the integer polynomial ring in two independent indeterminates t and s, indexed by zero and one respectively.", DescribeRole.Definition),
            Node("cigler-motzkin-hankel-defs-tvar", "The horizontal weight above the axis", "tVar",
                "The indeterminate t is the variable indexed by zero in the coefficient ring. It weights horizontal steps at positive height.", DescribeRole.Definition),
            Node("cigler-motzkin-hankel-defs-svar", "The horizontal weight on the axis", "sVar",
                "The indeterminate s is the variable indexed by one in the coefficient ring. It weights horizontal steps at height zero.", DescribeRole.Definition),
            Node("cigler-motzkin-hankel-defs-motzkin", "Boundary-weighted Motzkin polynomials", "motzkin",
                "For nonnegative integers n and k, M_{n,k}(t,s) sums the weights of paths from (0,0) to (n,k) with steps (1,1), (1,0) and (1,-1), never below the axis. Up and down steps have weight one; horizontal steps have weight s on the axis and t above it. Initially M_{0,0} = 1 and M_{0,k} = 0 for positive k. The last-step recurrence is M_{n+1,k} = M_{n,k-1} + w_k M_{n,k} + M_{n,k+1}, with the first term omitted at k = 0, w_0 = s and w_k = t for positive k.", DescribeRole.Definition),
            Node("cigler-motzkin-hankel-defs-hankeldet", "Shifted Hankel determinants", "hankelDet",
                "For nonnegative integers m and n, d_m(n,t,s) is the determinant of the n by n matrix whose entry in row i and column j is M_{m+i+j,0}(t,s), with i and j ranging from zero to n minus one. The determinant of the empty matrix is one.", DescribeRole.Definition),
            Node("cigler-motzkin-hankel-defs-lucas", "Lucas-type polynomials", "lucas",
                "The polynomials L_r(t) satisfy L_0 = 2, L_1 = t and L_{r+2} = t L_{r+1} - L_r for every nonnegative integer r.", DescribeRole.Definition),
            Node("cigler-motzkin-hankel-defs-factora", "The denominator factors", "factorA",
                "As polynomials in x over the coefficient ring, A_{0,0}(x,t) = 1 - x and A_{0,r}(x,t) = 1 - L_r(t)x + x squared for every positive integer r.", DescribeRole.Definition),
            Node("cigler-motzkin-hankel-defs-denominator", "The specified denominator", "denominator",
                "For every nonnegative integer m, Q_m(x,t) is the product of A_{0,m-2j}(x,t) raised to the exponent 1 + j(m-j), over integers j from zero through the integer part of m divided by two.", DescribeRole.Definition),
            Node("cigler-motzkin-hankel-defs-claim", "Cigler's boundary-weighted Hankel identity", "claim",
                "For every integer m at least one, there is a polynomial R_m(x,t,s) with integer coefficients such that R_m = Q_m times the formal series summing d_m(n,t,s)x^n over all nonnegative integers n, and the degree of R_m in x is exactly binom(m+1,3) + 1. The identity is an equality of formal power series over the integer polynomial ring in t and s. It is Conjecture 2.1, equation (2.3), of Cigler's paper.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
