using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KarpZhangGamma;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Paired reciprocal-gamma kernels and the two-variable transform.",
        H("Pairing and the transformed Turanian"), Blocks(
            Entry("karp-zhang-gamma-paired-kernel", "pairedKernel", "Paired scalar kernel",
                "For real a,alpha,beta and natural m,k, pairedKernel(a,alpha,beta,m,k) is kernel(a,alpha,beta,m,k) plus kernel(a,alpha,beta,m,m-k) when 2k < m, and is kernel(a,alpha,beta,m,k) otherwise. The theorems use only 0 <= k <= floor(m/2); the unique middle term in even degree is counted once.", DescribeRole.Definition),
            Entry("karp-zhang-gamma-paired-kernel-sign", "pairedKernel_sign", "One negative-to-positive sign change",
                "For every positive real a, nonnegative real alpha,beta and natural m, take any natural i,j <= floor(m/2) with i < j. If pairedKernel(a,alpha,beta,m,i) is positive, pairedKernel(a,alpha,beta,m,j) is nonnegative. This is the sign condition needed for the finite weighting principle and includes either shift being zero. The proof propagates a nonpositive four-term bracket backwards in the index, then argues by contradiction against a positive earlier bracket.", DescribeRole.Theorem),
            Entry("karp-zhang-gamma-finite-pairing", "finite_pairing", "Finite pairing with symmetric weights",
                "For real a,alpha,beta, natural m and a real sequence W satisfying W(m-k)=W(k) for every k <= m, the sum of kernel(a,alpha,beta,m,k) times W(k) over k=0,...,m equals the sum of pairedKernel(a,alpha,beta,m,k) times W(k) over k=0,...,floor(m/2). Split the full interval into its lower half and strict upper half, and reflect the upper half by k maps to m-k. The strict split ensures that an even-degree middle term occurs once.", DescribeRole.Theorem),
            Entry("karp-zhang-gamma-paired-kernel-sum-nonneg", "pairedKernel_sum_nonneg", "Nonnegative total paired kernel",
                "For every positive real a, nonnegative real alpha,beta and natural m, the sum of pairedKernel(a,alpha,beta,m,k) over k=0,...,floor(m/2) is nonnegative. Apply finite_pairing with W identically one and use Kernel.kernel_sum_nonneg. Positivity of this total is not assumed as an additional hypothesis.", DescribeRole.Theorem),
            Entry("karp-zhang-gamma-transform-delta", "transformDelta", "A finite coefficient of the transformed Turanian",
                "For a real sequence y, real a,alpha,beta and natural N,m, transformDelta(y,a,alpha,beta,N,m) is the sum over k=0,...,m of kernel(a,alpha,beta,m,k) times Smoothing.productCoeff(r maps to y(2k+r),r maps to y(2(m-k)+r),N). It is the coefficient of z to degree N and w to degree m in the Turanian of H(a;z,w), where H has coefficient y(2j+r)/(r factorial times j factorial times Real.Gamma(a+j)) in degree (r,j). All sums defining a fixed coefficient are finite.", DescribeRole.Definition),
            Entry("karp-zhang-gamma-two-variable-nonneg", "two_variable_nonneg", "Coefficient form of Theorem 5",
                "For every real sequence y satisfying D5.S3.Analytic.KarpZhangReciprocal.Result.IsLogConcave, every positive real a, all nonnegative real alpha,beta and all natural N,m, transformDelta(y,a,alpha,beta,N,m) is nonnegative. There is no convergence or growth hypothesis. Commutativity of the finite smoothed convolution makes the weights symmetric; finite_pairing then expresses the coefficient in terms of pairedKernel. The one-sign-change theorem and nonnegative total supply the hypotheses of Smoothing.smoothed_weighting.", DescribeRole.Theorem),
            Paragraph(Text("For x=a+k, z=a+m-k and alpha <= beta, let u,v,r,s be the reciprocal Gamma products with first arguments x+alpha, x+beta, x and x+alpha+beta respectively. Gamma balancing gives r <= u <= v. If B=u+v-r-s is nonpositive, then v <= s and r <= s. With S=x+z+alpha+beta and F(t)=(t-1)/(S-t), Gamma recurrence writes the preceding bracket as F(x+alpha)B + v(F(x+beta)-F(x+alpha)) + r(F(x+alpha)-F(x)) - s(F(x+alpha+beta)-F(x+alpha)). The first term is nonpositive, and the rest is at most s times F(x+beta)-F(x)-F(x+alpha+beta)+F(x+alpha), which is nonpositive because F has increasing increments. The increment formula is beta times (S-1) divided by the product of the two positive endpoint denominators. Swapping alpha and beta covers the other shift order.")))));

    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/KarpZhangGamma/Result." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
