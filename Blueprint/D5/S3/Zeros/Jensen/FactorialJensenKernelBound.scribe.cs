using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Jensen;

internal sealed class FactorialJensenKernelBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A degree-uniform factorial Jensen polynomial kernel bound.",
        H("A degree-uniform factorial Jensen kernel bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("factorial-jensen-kernel-uniform-bound"),
                DeclarationHandle.Create("D5/S3/Zeros/Jensen/FactorialJensenKernelBound.factorial_jensen_kernel_uniform_bound"),
                H("The complete finite polynomial kernel in every degree"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let n >= 1, r >= 0, s >= 0 and M = max(r,s). Define f(n,k) = descFactorial(n,k)/(n^k (2k)!). The divided difference D_d(r,s) is the polynomial sum over 0 <= k < d of r^(d-1-k)s^k, including the zero-degree empty sum. For each 1 <= I <= n and 0 <= j < I, place f(n,I)f(n,j)r^js^j D_(I-j)(r,s) at every position (a,b)=(j+l,I-1-l), with 0 <= l < I-j. Summing these single-entry matrices defines T_n(r,s).")),
                    Paragraph(Text("Equivalently, for 0 <= a,b < n its entry sums j from max(0,a+b+1-n) through min(a,b), with I=a+b+1-j. This is the full finite polynomial divided-difference expression, with no division by r-s; the cases r=s, r=0 and s=0 stay in scope.")),
                    Paragraph(Text("Every entry is nonnegative. The total sum of entries is at most (1/2) cosh(sqrt(M))^2 and at most (1/2) exp(2 sqrt(M)). For every real coefficient vector v of dimension n, the absolute value of sum_(a,b) v_a (T_n)_(a,b) v_b is at most (1/2) exp(2 sqrt(M)) sum_a v_a^2. There is no factor depending on n in this energy bound.")),
                    Paragraph(Text("The proof first uses descFactorial(n,k) <= n^k. A fixed pair I>j occupies exactly I-j matrix positions, while its divided difference has another I-j monomials; both multiplicities are retained. Bound (I-j)^2 by I^2 and use I^2/(2I)! <= 1/[2(2I-2)!]. The remaining finite double sum is bounded by one half the square of the nonnegative even-factorial partial sum, then by Mathlib's power series for cosh(sqrt(M)). The elementary inequality cosh(x) <= exp(x) for x >= 0 supplies the exponential bound. Absolute finite-sum inequalities and |v_a v_b| <= sum_i v_i^2 give the quadratic bound.")),
                    Paragraph(Text("The exact coefficient correspondence with the existing source is sourceJensenPolynomial(n) = sum_(0<=k<=n) C(f(n,k) sourceThetaMoment(k)) X^k. It follows by substituting sourceThetaCoefficient(k) = sourceThetaMoment(k)/(2k)! into its existing definition. This adapter is an application of the existing source definitions; it adds no retained named mathematical declaration.")),
                    Paragraph(Text("This theorem bounds the complete finite polynomial amplification used in the actual theta matrix estimates. It supplies neither the sign of the integrated quadratic form for mixed-sign vectors nor positive semidefiniteness of that integrated matrix. Degree-dependent positive margins, the remaining moderate separated-coordinate comparison, the Riemann hypothesis and strict Robin for all n>5040 remain outside this conclusion."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering"))]));
}
