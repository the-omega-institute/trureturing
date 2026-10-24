using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KarpZhangReciprocal;

internal sealed class IntervalConvolutionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/karpzhang2023pochhammer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Balancing positive parameters in reciprocal Pochhammer interval convolutions.",
        H("Symmetric interval convolutions"), Blocks(
            Entry("karp-zhang-reciprocal-interval-convolution", "F", "Interval convolution",
                "For natural m, L, U and real s, t, F(m,L,U,s,t) is the sum of c(L+i,s)c(m-(L+i),t) over 0 <= i < U-L+1, with natural subtraction. When L <= U <= m this is exactly the convolution over L <= k <= U.", DescribeRole.Definition),
            Entry("karp-zhang-reciprocal-symmetric-tail", "symmetric_tail", "Balancing inequality",
                "For every natural m and q with 2q <= m, and reals 0 < a <= b <= c <= d satisfying a+d=b+c, F(m,q,m-q,a,d) <= F(m,q,m-q,b,c). Singleton intervals and equal parameters are included. This proves the symmetric-tail inequality needed for the reciprocal-Pochhammer half of Conjecture 5.2; it makes no assertion about the other half.", DescribeRole.Theorem),
            Entry("karp-zhang-reciprocal-shift-tail", "shift_tail", "Arbitrary nonnegative shifts",
                "For every natural m and q with 2q <= m, positive real mu, and nonnegative real alpha and beta, F(m,q,m-q,mu,mu+alpha+beta) <= F(m,q,m-q,mu+alpha,mu+beta). The shifts need not be ordered. This is the tail estimate consumed by the Abel reduction.", DescribeRole.Theorem),
            Paragraph(Text(
                "On a translated interval 0,...,n, normalize the positive coefficient products to probabilities. Use birth rate (m-k)lambda(k,s) below the upper endpoint and death rate k lambda(m-k,t) above the lower endpoint, with zero outward rates. The coefficient recurrence gives detailed balance. Antitonicity of lambda bounds edge curvature below by lambda(k,s)+lambda(m-k-1,t). The finite birth-and-death variance bound, a weighted square inequality, and chi(j,t) >= j eta(j-1,t)^2 absorb score variance into expected curvature. Differentiating log F(s,S-s) twice therefore gives a nonpositive second derivative. Mathlib's concavity criterion applies on the open interval (0,S). Reindexing k to m-k makes the two endpoint values equal, and the minimum principle for a concave function gives the balancing inequality.")))));

    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);
}
