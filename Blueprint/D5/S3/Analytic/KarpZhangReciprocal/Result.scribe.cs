using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KarpZhangReciprocal;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/karpzhang2023pochhammer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reciprocal-Pochhammer half of Karp-Zhang Conjecture 5.2.",
        H("Reciprocal coefficients and Abel reduction"), Blocks(
            Entry("karp-zhang-reciprocal-log-concave-sequence", "IsLogConcave", "The sequence convention",
                @"Definition 1.1, page 2: Let $\{f_k\}_{k=0}^{\infty}$ be a non-negative nontrivial real sequence. We call $\{f_k\}_{k=0}^{\infty}$ log-concave (or Pólya frequency two – $PF_2$, or doubly positive) if $f_k^2\ge f_{k-1}f_{k+1}$ for each $k\in\mathbb N$, and $\{f_k\}_{k=0}^{\infty}$ is supported on an interval of integers (i.e., $f_N=0$ implies either $f_{N+i}=0$ for all $i\in\mathbb N_0$ or $f_{N-i}=0$ for $i=0,\ldots,N$). The Lean predicate retains all four conditions: nonnegativity at every natural index, an index with nonzero value, the adjacent-product inequality for k >= 1, and the stated disjunction for every zero entry. Natural subtraction is used only with the stated bounds.", DescribeRole.Definition),
            Entry("karp-zhang-reciprocal-turanian-coefficient", "delta", "Finite Cauchy coefficient",
                "For a real sequence y, real mu, alpha, beta and natural m, delta(y,mu,alpha,beta,m) is the sum over k=0,...,m of y(k)y(m-k) times [c(k,mu+alpha)c(m-k,mu+beta)-c(k,mu)c(m-k,mu+alpha+beta)]. It is exactly the degree-m coefficient of the difference of the two formal Cauchy products of the reciprocal series. No analytic convergence hypothesis is imposed.", DescribeRole.Definition),
            Entry("karp-zhang-reciprocal-abel-reduction", "abel_reduction", "Abel summation identity",
                "For every real sequence y, real mu, alpha, beta and natural m, put h=floor(m/2), W(q)=y(q)y(m-q), and T(q)=F(m,q,m-q,mu+alpha,mu+beta)-F(m,q,m-q,mu,mu+alpha+beta). Then delta=W(0)T(0)+sum over q=0,...,h-1 of [W(q+1)-W(q)]T(q+1). The identity holds without positivity assumptions. The even central index is counted once, because each T is an unpaired interval sum.", DescribeRole.Theorem),
            Entry("karp-zhang-reciprocal-half", "reciprocal_half", "All coefficients are nonnegative",
                "For every sequence y satisfying IsLogConcave, positive real mu, nonnegative real alpha and beta, and every natural m, 0 <= delta(y,mu,alpha,beta,m). This proves the reciprocal-Pochhammer assertion of Conjecture 5.2 on page 12 under exactly the sequence convention of Definition 1.1. It does not assert the corresponding gamma-series half.", DescribeRole.Theorem),
            Paragraph(Text(
                "The interval-support condition forces every entry between two positive entries to be positive. Divide the adjacent log-concavity inequalities only on such positive intervals and induct to compare distant successive ratios. Consequently W(q+1) >= W(q) below the middle; if W(q)=0, nonnegativity gives the same conclusion directly. Telescoping the increments of W expresses W(min(k,m-k)) as a sum of layers. Interchanging two finite sums turns each layer into a symmetric tail and proves the Abel identity. The interval-convolution balancing theorem makes each tail nonnegative, and every Abel weight is nonnegative. Thus each formal coefficient is nonnegative independently of growth or convergence of the infinite series.")))));

    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/KarpZhangReciprocal/Result." + name),
            H(title), StatementSource.WithoutFormula(),
            name == "IsLogConcave" || name == "delta"
                ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);
}
