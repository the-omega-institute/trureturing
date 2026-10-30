using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CatalanPowerHankel;

internal sealed class CiglerSixteenDegreeRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/CatalanPowerHankel/CiglerSixteenDegreeRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/cigler2023catalanpowers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal exact-degree requirement in Cigler's v2 Conjecture 16 fails at k=1 and m=0.",
        H("The degree boundary in Cigler's Conjecture 16"),
        Blocks(
            Paragraph(Text(
                "The source is Johann Cigler's arXiv:2308.07642v2, Section 3, "
                    + "Conjecture 16, equation (30), on page 10. Its Catalan coefficients "
                    + "and determinant conventions appear in equations (1) and (2) on "
                    + "page 1; reciprocity and second polygonal numbers are defined on "
                    + "page 9. The conjecture is interpreted coefficientwise over the "
                    + "complex numbers. There is no analytic convergence hypothesis.")),
            Node("cigler-sixteen-catalan", "The actual Catalan series", "catalanSeries",
                "For a commutative ring R, C(x) is Mathlib's natural Catalan series "
                    + "with coefficients cast into R: its coefficient at n is the "
                    + "Catalan number binom(2n,n)/(n+1). In particular its constant "
                    + "coefficient is one. The sequence is not defined by a Hankel "
                    + "evaluation or a conjectured numerator.", DescribeRole.Definition),
            Node("cigler-sixteen-convolution", "Convolution coefficients and negative indices",
                "catalanPowerCoeff",
                "For a natural r and an integer t, C_{r,t} is the coefficient at t "
                    + "of C(x)^r when t is nonnegative, and zero when t is negative. "
                    + "The claim uses only positive r. This is the source's defining "
                    + "convolution interpretation; no closed-form coefficient bridge "
                    + "is assumed.", DescribeRole.Definition),
            Node("cigler-sixteen-hankel", "Every finite Hankel determinant", "hankel",
                "For a commutative ring R, a natural r, an integer m and a natural N, "
                    + "D_{r,m}(N) is the determinant of the matrix C_{r,i+j+m}, with "
                    + "i and j ranging through Fin N. Negative shifts retain their "
                    + "integer meaning. The empty determinant D_{r,m}(0) is one.",
                DescribeRole.Definition),
            Node("cigler-sixteen-series", "The full determinant generating series", "hankelSeries",
                "For R, r and m as above, F_{r,m}(x) has coefficient D_{r,m}(N) "
                    + "at every natural N. It is the entire formal series, with no "
                    + "truncation and no selected determinant sizes.", DescribeRole.Definition),
            Node("cigler-sixteen-polygonal", "Second polygonal numbers", "polygonalNumber",
                "For integers j and t, pi_j(t) is t((j-2)t+(j-4))/2, evaluated "
                    + "in the rationals. The source uses j at least three. Thus "
                    + "pi_3(t)=t(t-1)/2, including pi_3(0)=0; the subtraction "
                    + "j-4 is not truncated natural subtraction.", DescribeRole.Definition),
            Node("cigler-sixteen-numerator", "The product in equation (30)", "numeratorSeries",
                "For a commutative ring R and integers k and m, the numerator "
                    + "series is (1+(-1)^k x^(2k-1))^(binom(k+m,2)+1) times "
                    + "F_{2k-1,m}(x), using natural conversions for its exponents "
                    + "and binomial argument. In the claimed range k is at least "
                    + "one and m is at least 1-k: consequently k, 2k-1 and k+m "
                    + "are positive, so every such conversion preserves its "
                    + "integer value. The shift m is never converted to a natural.",
                DescribeRole.Definition),
            Node("cigler-sixteen-palindromic", "Palindromicity at actual degree", "palindromic",
                "For a complex polynomial Q of actual degree d, palindromicity "
                    + "means x^d Q(1/x)=Q(x) at every nonzero complex x. The "
                    + "exponent is Q.natDegree, which equals the actual degree "
                    + "when Q is nonzero. The exact-degree clause below excludes "
                    + "the zero polynomial.", DescribeRole.Definition),
            Node("cigler-sixteen-skew", "Skew palindromicity at actual degree", "skewPalindromic",
                "For a complex polynomial Q of actual degree d, skew "
                    + "palindromicity means x^d Q(1/x)=-Q(x) at every nonzero "
                    + "complex x, with the same actual-degree convention.", DescribeRole.Definition),
            Node("cigler-sixteen-claim", "The whole literal Conjecture 16", "claim",
                "For every integer k at least one and every integer m at least "
                    + "1-k, there exists a complex polynomial Q such that the "
                    + "full numerator series equals Q and its actual degree is "
                    + "pi_{2k+1}(m+k-1)+k. Formally, there is a natural d with "
                    + "Q.degree=d and d equal to that rational expression; this "
                    + "is an exact degree equality and implies Q is nonzero. "
                    + "Every Q is either palindromic or skew palindromic. It is "
                    + "palindromic if k is 1 modulo 4 and m is even, if k is 3 "
                    + "modulo 4 and m is odd, and if k is 0 or 2 modulo 4 and "
                    + "m is 0 or 1 modulo 4. These are implications, with no "
                    + "converses or additional sign rule. All permitted negative "
                    + "shifts and the boundary k=1 remain in the claim.", DescribeRole.Definition),
            Node("cigler-sixteen-result", "The literal conjecture is false", "result",
                "Take k=1 and m=0. The multiplier is 1-x and the demanded "
                    + "degree is pi_3(0)+1=1. The true empty determinant and "
                    + "the true singleton determinant are both one: the latter "
                    + "is C_{1,0}, the constant coefficient of the actual Catalan "
                    + "series. Therefore the linear coefficient of (1-x)F_{1,0} "
                    + "is D_{1,0}(1)-D_{1,0}(0)=0. Polynomial-to-series "
                    + "coefficient compatibility makes Q's linear coefficient "
                    + "zero, whereas exact degree one makes it nonzero. This "
                    + "contradicts one conjunct of the whole universal assertion. "
                    + "The coefficient obstruction is proved over every "
                    + "commutative ring, and thus also holds directly for "
                    + "integer, rational and real polynomials. It does not "
                    + "depend on a rational-only restriction or any convention "
                    + "for the degree of zero.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("cigler-sixteen-literal-numerator-degree"),
                    ResolutionKind.Refuted)),
            Paragraph(Text(
                "Equation (6), on page 2, already records the well-known "
                    + "all-order identities D_{1,0}(N)=D_{1,1}(N)=1. No new "
                    + "determinant evaluation is asserted. The paragraph after "
                    + "(30) calls k=1 'not optimal' and prints "
                    + "Q_{1,m+1}(x)=(x-1)^(m+1)P_{2,m}(x). In the m at least "
                    + "zero range inherited from (29), that shifted relation "
                    + "does not include Q_{1,0}; it neither removes that "
                    + "boundary from the conjecture nor retracts its exact "
                    + "degree equality. Its sign is retained as printed and "
                    + "is not used in the proof. The different v1 Conjecture "
                    + "16 becomes v2 Conjecture 18. No repaired degree bound, "
                    + "k at least two conjecture, or worldwide priority is "
                    + "asserted here."))), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
