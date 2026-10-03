using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MotzkinHankel;

internal sealed class CiglerMotzkinHankelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinHankel.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2022motzkin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cigler's boundary-weighted Motzkin Hankel series has the specified denominator and a numerator of exact degree binom(m+1,3) + 1 for every positive shift m.",
        H("Cigler's Boundary-Weighted Motzkin Hankel Formula"),
        Blocks(
            Node("cigler-motzkin-hankel-result", "The boundary-weighted generating function", "result", "For every integer m at least one, let M_{n,k}(t,s) sum the weights of Motzkin paths from (0,0) to (n,k) never below the axis, with up and down steps weighted one, horizontal steps on the axis weighted s, and horizontal steps above it weighted t. Put d_m(n,t,s) = det(M_{m+i+j,0}(t,s)) for indices i and j from zero to n minus one. Define L_0 = 2, L_1 = t and L_{r+2} = t L_{r+1} - L_r, and set A_{0,0}(x,t) = 1 - x and A_{0,r}(x,t) = 1 - L_r(t)x + x squared for positive r. There is an integer polynomial R_m(x,t,s) of exact x-degree binom(m+1,3) + 1 such that the formal series summing d_m(n,t,s)x^n over all nonnegative n, multiplied by the product of A_{0,m-2j}(x,t)^(1+j(m-j)) for j from zero through the integer part of m divided by two, equals R_m. This establishes Conjecture 2.1, equation (2.3), of Cigler's paper. Orthogonal coefficient determinants and their two reciprocal branches give polynomial factors of degree at most j(m-j) in the index n. Alternant confluence gives the denominator exponents, and the first nonzero negative-index determinant fixes the numerator degree. The identity holds over the integer polynomial ring in t and s, so it remains valid under specialization, including repeated reciprocal roots. The exact degree is asserted over that ring; specialization can lower it. The denominator is the specified common denominator, without an assertion that the numerator is relatively prime to it.", DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("cigler-boundary-motzkin-hankel"), ResolutionKind.Proved))
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
