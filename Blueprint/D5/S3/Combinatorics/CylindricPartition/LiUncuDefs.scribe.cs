using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CylindricPartition;

internal sealed class LiUncuDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CylindricPartition/LiUncuDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QSeries/li2025macmahon");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian binomials with a primed boundary convention define the two polynomial sums in the finite Andrews-Gordon companion identity.",
        H("The Finite Andrews-Gordon Companion Polynomials"),
        Blocks(
            Node("li-uncu-defs-gauss", "Gaussian polynomials", "gauss",
                "For nonnegative integers a and b, G(a,0) = 1 and G(0,b+1) = 0. The recurrence G(a+1,b+1) = G(a,b+1) + q^(a-b) G(a,b) defines the Gaussian polynomial, with natural-number subtraction in the exponent.", DescribeRole.Definition),
            Node("li-uncu-defs-gaussint", "Integer-indexed Gaussian polynomials", "gaussInt",
                "For integers a and b, the Gaussian polynomial is zero when either index is negative, and otherwise is G(a,b) with nonnegative indices. It also vanishes when b exceeds a.", DescribeRole.Definition),
            Node("li-uncu-defs-gaussprime", "The primed boundary convention", "gaussPrime",
                "The primed Gaussian polynomial equals one whenever its lower index is zero, even if the upper index is negative. For every other lower index it equals the integer-indexed Gaussian polynomial.", DescribeRole.Definition),
            Node("li-uncu-defs-alpha", "The boundary shift", "alpha",
                "For nonnegative integers i and j, alpha(i,j) is the maximum of j - i + 1 and zero, computed in the integers.", DescribeRole.Definition),
            Node("li-uncu-defs-entry", "Tuple entries with zero extension", "entry",
                "A tuple has k - 1 entries between zero and n. Its jth entry is read with indices starting at one when 1 is at most j and j is at most k - 1; all other entries are zero.", DescribeRole.Definition),
            Node("li-uncu-defs-leftterm", "A multiple-sum term", "leftTerm",
                "Write n_j for the zero-extended tuple entries. The term is q raised to the sum of n_j squared for j from one to k - 1 plus the sum of n_j for j from i to k - 1, multiplied by the primed Gaussian factors with upper index 2n - 2 times the sum of n_l for 1 at most l and l less than j, minus n_j, n_(j+1), and 2 alpha(i,j), and lower index n_j - n_(j+1). The product runs from j = 1 through k - 1. Exponents are converted to nonnegative integers by truncation at zero.", DescribeRole.Definition),
            Node("li-uncu-defs-lhs", "The finite multiple sum", "lhs",
                "The left polynomial is the sum of leftTerm over all weakly decreasing tuples of k - 1 entries between zero and n.", DescribeRole.Definition),
            Node("li-uncu-defs-rightterm", "An alternating Gaussian term", "rightTerm",
                "For an integer r, put epsilon = 0 when r is even and epsilon = -1 when r is odd. The term is (-1)^abs(r) times q raised to r((2k+1)r + 2k - 2i + 1)/2, multiplied by the integer-indexed Gaussian polynomial with upper index 2n and lower index (2n - (2k+1)r + (2k-2i+1)epsilon)/2. Integer division is used and the exponent is truncated at zero before taking the power.", DescribeRole.Definition),
            Node("li-uncu-defs-rhs", "The finite alternating sum", "rhs",
                "The right polynomial is the sum of rightTerm over all integers r from -(n+1) through n+1, inclusive.", DescribeRole.Definition),
            Node("li-uncu-defs-claim", "The companion identity", "claim",
                "For every nonnegative integer n, every integer k at least five, and every integer i with 1 at most i and i less than k, the finite multiple sum lhs(n,k,i) equals the finite alternating sum rhs(n,k,i) as polynomials with integer coefficients.", DescribeRole.Definition)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
