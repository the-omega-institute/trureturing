using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KarpZhangGamma;

internal sealed class KernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite reciprocal-gamma convolution and its total kernel.",
        H("Reciprocal-gamma sum identity"), Blocks(
            Entry("karp-zhang-gamma-reciprocal-gamma-sum", "reciprocalGamma_sum", "Closed form for the finite convolution",
                "For positive real b,c and every natural m, the sum over k=0,...,m of 1/[k factorial times (m-k) factorial times Real.Gamma(b+k) times Real.Gamma(c+m-k)] equals the evaluation of ascPochhammer at b+c+m-1 in degree m, divided by m factorial times Real.Gamma(b+m) times Real.Gamma(c+m). This is identity (3.11) of the gamma-series argument. It includes m=0 even when b+c-1 is nonpositive.", DescribeRole.Theorem),
            Entry("karp-zhang-gamma-kernel", "kernel", "Unpaired scalar kernel",
                "For real a,alpha,beta and natural m,k, kernel(a,alpha,beta,m,k) equals 1/[k factorial times (m-k) factorial] times the difference between 1/[Real.Gamma(a+alpha+k)Real.Gamma(a+beta+m-k)] and 1/[Real.Gamma(a+k)Real.Gamma(a+alpha+beta+m-k)]. Natural subtraction is literal; the theorems sum only over k <= m.", DescribeRole.Definition),
            Entry("karp-zhang-gamma-kernel-sum-nonneg", "kernel_sum_nonneg", "Nonnegative total kernel",
                "For every positive real a, nonnegative real alpha,beta and natural m, the sum of kernel(a,alpha,beta,m,k) for k=0,...,m is nonnegative. The convolution formula factors this total as the rising-factorial prefactor divided by m factorial, times the reciprocal-gamma balancing difference at a+m. Jensen's inequality for Real.convexOn_log_Gamma makes that difference nonnegative. At m=0 the rising-factorial prefactor is one; at positive degree its argument is positive.", DescribeRole.Theorem),
            Paragraph(Text("The finite Pascal recurrence and Real.Gamma_add_one prove the convolution identity by induction, simultaneously for every pair of positive parameters. This is a finite Vandermonde recurrence: the two shifted-parameter terms have the same rising-factorial numerator, and their denominator combination supplies its next factor. The module proves the unweighted sum assertion only. The paired-kernel one-sign-change theorem, the unconditional two-variable transform theorem and the final identification with the original gamma series remain separate obligations.")))));

    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/KarpZhangGamma/Kernel." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
