using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KarpZhangReciprocal;

internal sealed class BirthDeathDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/karpzhang2023pochhammer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite variance inequality for reversible birth-and-death rates.",
        H("Variance and edge curvature"), Blocks(
            Entry("karp-zhang-birth-death-curvature", "kappa", "Edge curvature",
                "For all real sequences p and r and every natural i, kappa(p,r,i) equals p(i)-p(i+1)+r(i+1)-r(i).", DescribeRole.Definition),
            Entry("karp-zhang-birth-death-variance", "variance", "Finite variance",
                "For a natural n and real sequences pi and h, set a equal to the sum of pi(j)h(j) over 0 <= j <= n. Then variance(n,pi,h) is the sum over 0 <= i <= n of pi(i) times (h(i)-a) squared. Under probability normalization this is the usual variance.", DescribeRole.Definition),
            Entry("karp-zhang-birth-death-variance-bound", "variance_bound", "Curvature-weighted variance bound",
                "Let n be any natural number. Suppose pi is positive on the vertices 0,...,n and sums to one there. Let p(n)=r(0)=0, let p(i)>0 for i<n, and let r(i)>0 for 0<i<=n. Assume detailed balance pi(i)p(i)=pi(i+1)r(i+1) and positive kappa(p,r,i) for every i<n. Then, for every real sequence h, variance(n,pi,h) is at most the sum over 0 <= i < n of pi(i)p(i)/kappa(p,r,i) times (h(i+1)-h(i)) squared. The hypotheses allow n=0, when the variance and the edge sum vanish.", DescribeRole.Theorem),
            Paragraph(Text(
            "Center h by its pi mean. An edge flux z is obtained by taking the negative cumulative centered mass and dividing by the edge weight. It satisfies h(i)=r(i)z(i)-p(i)z(i+1). Detailed balance converts the variance into the edge sum of pi(i)p(i)(h(i+1)-h(i))z(i+1). A pointwise square inequality and the same balance identity bound the sum of pi(i)p(i)kappa(i)z(i+1) squared by the variance. Weighted Cauchy-Schwarz then gives the stated estimate. All sums are finite, and no inverse operator or limiting argument is needed.")))));

    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/KarpZhangReciprocal/BirthDeath." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);
}
