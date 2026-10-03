using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MotzkinHankel;

internal sealed class CiglerMotzkinColumnDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MotzkinHankel/CiglerMotzkinColumn.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/cigler2022motzkin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At every positive shift, each Motzkin-triangle column has Cigler's specified Hankel-series denominator and a numerator of the exact stated degree.",
        H("Cigler's Motzkin-Column Hankel Formula"),
        Blocks(
            Node("cigler-motzkin-column-result", "The generating function of a Motzkin-column Hankel determinant", "result", "For every nonnegative integer k and every integer m at least one, let M_{n,k}(t) sum the weights of Motzkin paths from (0,0) to (n,k) never below the axis, with up and down steps of weight one and all horizontal steps of weight t. Put d_m^{(k)}(n,t) = det(M_{m+i+j,k}(t)) for indices i and j from zero to n minus one, with empty determinant one. Define L_0 = 2, L_1 = t and L_{r+2} = t L_{r+1} - L_r, and put e = (-1)^binom(k+1,2). Set A_{k,0}(x,t) = 1 - e x^(k+1) and A_{k,r}(x,t) = 1 - e L_r(t)x^(k+1) + x^(2(k+1)) for positive r. There is an integer polynomial R_m^{(k)}(x,t) of exact x-degree binom(m+1,3) + k(binom(m,1) + binom(m,2) + binom(m,3)) such that the formal series summing d_m^{(k)}(n,t)x^n over all nonnegative n, multiplied by the product of A_{k,(k+1)(m-2j)}(x,t)^(1+j(m-j)) over j from zero through the integer part of m divided by two, equals R_m^{(k)}. This establishes Conjecture 1.3, equation (1.30), of Cigler's paper. Monic remainder determinants give a mixed alternant with m confluent nodes and k fixed Chebyshev nodes. Reciprocal branches bound its polynomial modes by j(m-j), and the first nonzero negative-index determinant fixes the numerator degree. The identity holds over the integer polynomial ring in t and therefore under every specialization of t. The exact degree is asserted over that ring; specialization can lower it. The specified denominator is a common denominator, without an assertion that numerator and denominator are relatively prime.", DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("cigler-motzkin-column-hankel"), ResolutionKind.Proved))
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
