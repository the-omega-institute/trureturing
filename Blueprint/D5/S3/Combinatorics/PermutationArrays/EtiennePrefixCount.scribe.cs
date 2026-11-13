using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PermutationArrays;

internal sealed class EtiennePrefixCountDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/hardin2011a183409");

    private static DocumentBlock Definition(string name, string title, string explanation) =>
        Describe.Lean(
            DescribeId.Create("etienne-definition-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/PermutationArrays/EtiennePrefixCount." + name),
            H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sorted binary matrices with bounded top-left rectangle sums.",
        H("Etienne's width-two prefix matrices"),
        Blocks(
            Definition("Matrix", "Labeled binary matrices",
                "A height-n matrix is a function from Fin n to Fin 2 to Bool."),
            Definition("rank", "Lexicographic row rank",
                "Twice the left bit plus the right bit orders the four rows as 00,01,10,11."),
            Definition("ColumnsLE", "Weak column order",
                "The column words agree everywhere, or their first unequal row has left zero and right one."),
            Definition("cell", "Natural-indexed entries",
                "Inside the matrix this is the bit as a natural number; outside it the value is zero."),
            Definition("ones", "Rectangle sums",
                "The sum counts ones at row indices below i and column indices below j."),
            Definition("PrefixBound", "All top-left rectangle bounds",
                "For every positive i at most n and positive j at most two, twice the rectangle sum is at most i*j."),
            Definition("Admissible", "The literal constraints",
                "The row-rank function is monotone, the columns are weakly lexicographically ordered, and every in-bounds prefix satisfies its bound."),
            Definition("a", "The literal matrix count",
                "The count is Nat.card of Arrays n, independently of any closed formula."),
            Definition("Cuts", "Four consecutive blocks",
                "Three natural cuts satisfy p<=q<=r<=n. Empty blocks are allowed."),
            Definition("blockMatrix", "Reconstruction from cuts",
                "The reconstructed matrix has rows 00 before p, 01 from p to q, 10 from q to r, and 11 thereafter."),
            Describe.Lean(
                DescribeId.Create("literal-prefix-matrix-carrier"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/PermutationArrays/EtiennePrefixCount.Arrays"),
                H("Actual labeled matrices"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("The objects are actual functions from Fin n to Fin 2 to Bool. "
                        + "The rank of a row is twice its left bit plus its right bit. "
                        + "Thus the weak row order is exactly 00,01,10,11. Columns are words "
                        + "read from top to bottom: either all corresponding bits agree, "
                        + "or their first difference is a zero in the left column and a one "
                        + "in the right column. Repeated rows and equal columns are retained; "
                        + "there is no quotient by permutations or symmetries.")),
                    Paragraph(Text("For every i from one through n and j from one through two, "
                        + "twice the number of ones in the top-left i by j rectangle is at most i*j. "
                        + "The zero extension in cell only provides natural indices for the "
                        + "finite sums; these bounds keep every tested cell inside the matrix. "
                        + "The function a is Nat.card of exactly this subtype, independently "
                        + "of a closed formula."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("etienne-full-integer-formula"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/PermutationArrays/EtiennePrefixCount.claim"),
                H("The all-height formula"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every natural height n at least one, the assertion is "
                    + "32*a(n)=2*n^3+11*n^2+31*n+27+(n^2+n+5)*(-1)^n, with signed integer "
                    + "arithmetic. It is the entire second FORMULA in OEIS A183409. "
                    + "The empirical recurrence and generating function listed separately "
                    + "in that entry are not premises of this assertion."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("etienne-literal-matrix-cardinality"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/PermutationArrays/EtiennePrefixCount.result"),
                H("Cardinality by the four row blocks"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("A sorted matrix has four consecutive blocks 00,01,10,11. "
                        + "The cuts p,q,r count ranks strictly below one, two and three. "
                        + "For a monotone word every strict sublevel set is an initial segment, "
                        + "so these three sizes reconstruct every entry at its original position. "
                        + "Conversely the block construction is monotone and its cuts are unique. "
                        + "The equivalence of actual matrices with valid cuts includes both inverse laws.")),
                    Paragraph(Text("Write A=p, B=q-p, C=r-q and D=n-r. Their sum is n. "
                        + "The column comparison is equivalent to B>0 or C=0. "
                        + "At every prefix height i, the first column has i-q ones, using "
                        + "natural subtraction. The two-column rectangle has (i-p)+(i-r) ones. "
                        + "These identities show that all rectangle bounds are equivalent "
                        + "to C+D<=A+B and D<=A; the reverse implication uses the same "
                        + "prefix identities for each i, not only the full-height rectangle.")),
                    Paragraph(Text("Set t=C+D, d=D and u=n-t. Then t ranges from zero through "
                        + "floor(n/2), and d ranges from zero through t. If d<t, the admissible "
                        + "values of A form the half-open interval from d to u. If d=t, "
                        + "the interval includes u. The last coordinate is A-d, with respective "
                        + "sizes u-d and u-d+1. Reconstruction gives B=u-A, C=t-d and D=d. "
                        + "The inverse laws also hold at zero-length blocks and interval endpoints.")),
                    Paragraph(Text("The inner sum has one extra endpoint, at d=t. Mathlib's "
                        + "finite arithmetic-series identity evaluates its doubled cardinality; "
                        + "summing the fibers gives 2*a(n)=2*(m+1)+(n-m)*(m+1)*(m+2), "
                        + "where m=floor(n/2). The two possibilities n=2*m and n=2*m+1 "
                        + "then give the signed formula. In particular, the sole equal-column "
                        + "matrix at each t is retained. The boundary n=1 and the even endpoint "
                        + "t=n/2 require no separate exclusion."))), DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a183409-etienne-prefix-count"),
                    ResolutionKind.Proved)))));
}
