using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KarpZhangGamma;

internal sealed class SmoothingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coefficientwise balancing of exponential derivatives.",
        H("Finite exponential smoothing"), Blocks(
            Entry("karp-zhang-gamma-binomial-product", "binomialProduct", "Factorial-scaled coefficient",
                "For real sequences f,g and natural N, binomialProduct(f,g,N) is the sum over r=0,...,N of Nat.choose(N,r) times f(r)g(N-r), with the binomial coefficient cast to the reals. It is N factorial times the ordinary coefficient of the product of the exponential generating series of f and g.", DescribeRole.Definition),
            Entry("karp-zhang-gamma-product-coeff", "productCoeff", "Ordinary coefficient",
                "For real sequences f,g and natural N, productCoeff(f,g,N) is the sum over r=0,...,N of f(r)g(N-r) divided by r factorial times (N-r) factorial. This is an ordinary finite Cauchy coefficient, without convergence assumptions.", DescribeRole.Definition),
            Entry("karp-zhang-gamma-balanced-product", "balanced_product", "General balancing inequality",
                "Let y satisfy D5.S3.Analytic.KarpZhangReciprocal.Result.IsLogConcave. For natural L,R,u,v satisfying L <= u, L <= v, u <= R, v <= R and u+v=L+R, y(L)y(R) <= y(u)y(v). The proof reuses the existing balanced_step theorem at fixed index sum, including sequences whose lower support boundary is positive.", DescribeRole.Theorem),
            Entry("karp-zhang-gamma-binomial-product-succ", "binomialProduct_succ", "Finite Leibniz recurrence",
                "For every pair of real sequences f,g and natural N, binomialProduct(f,g,N+1) equals binomialProduct(r maps to f(r+1),g,N) plus binomialProduct(f,r maps to g(r+1),N). This follows from Pascal's identity, retaining both endpoint terms exactly.", DescribeRole.Theorem),
            Entry("karp-zhang-gamma-product-coeff-eq", "productCoeff_eq", "Factorial conversion",
                "For every pair of real sequences f,g and natural N, productCoeff(f,g,N) equals binomialProduct(f,g,N) divided by N factorial. Nat.choose_mul_factorial_mul_factorial supplies the finite coefficient identity; factorials are positive.", DescribeRole.Theorem),
            Entry("karp-zhang-gamma-smoothing-minor", "smoothing_minor", "Every smoothed minor is nonnegative",
                "For every real sequence y satisfying IsLogConcave and all natural p,q,N with p <= q+1, productCoeff(r maps to y(p+r),r maps to y(q+2+r),N) <= productCoeff(r maps to y(p+1+r),r maps to y(q+1+r),N). Thus the degree-N coefficient of P(p+1)P(q+1)-P(p)P(q+2) is nonnegative, where P(j) has coefficient y(j+r)/r factorial in degree r. The adjacent-index boundary p=q+1 is equality.", DescribeRole.Theorem),
            Entry("karp-zhang-gamma-smoothed-weighting", "smoothed_weighting", "Weighted transformed minors",
                "Let y satisfy IsLogConcave, let A be a real sequence and m a natural number, and put h=floor(m/2). Assume that for all i,j <= h with i < j, A(i)>0 implies A(j)>=0, and that the sum of A(i) for i=0,...,h is nonnegative. Then for every natural degree N, the sum over k=0,...,h of A(k) times productCoeff(r maps to y(2k+r),r maps to y(2(m-k)+r),N) is nonnegative. The sign and total-sum hypotheses concern A alone.", DescribeRole.Theorem),
            Paragraph(Text("Induct simultaneously in the coefficient degree for all derivative-index pairs. The finite Leibniz recurrence makes the next minor the sum of two current minors because the middle products cancel. At the adjacent-index boundary one minor is zero by commutativity. The constant coefficient is the general balancing inequality, obtained by repeated use of the existing balanced_step theorem. Two consecutive balancing steps make P(2k)P(2(m-k)) increase up to the middle; the weighting principle then gives the last theorem. This finite induction proves the same coefficient inequality as the finite Cauchy-Binet argument, without introducing power series or convergence hypotheses.")))));

    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/KarpZhangGamma/Smoothing." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
