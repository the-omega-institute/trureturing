using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.ZeroDivisor;

internal sealed class NormalizedCurvatureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/ZeroDivisor/NormalizedCurvature.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Second differences of normalized binomial coefficients and their uniform bounds.",
        H("Normalized binomial curvature"),
        Blocks(
            Describe.Lean(DescribeId.Create("normalized-second-difference"),
                DeclarationHandle.Create(Prefix + "normalized_second_difference"),
                H("Exact second difference"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let N, m and k be natural numbers with m at most N and 1 at most k less than N. Write h(j)=choose(m,j)/choose(N,j), using rational division. Then h(k-1)-2h(k)+h(k+1) equals H(N,m,k)=choose(m,k-1) choose(N-m,2) divided by choose(N,k+1) choose(k+1,2). All binomial coefficients and their indices use natural numbers, so a coefficient with its lower index above its upper index is zero.")),
                    Paragraph(Text("The adjacent-coefficient recurrence, interpreted over the rationals, remains valid even beyond the natural support because both coefficients vanish. Apply it twice in each row and use choose(a,2)=a(a-1)/2 over the rationals. The resulting numerator factors as choose(m,k-1)(N-m)(N-m-1). The denominators are positive on the stated interval. This includes k=N-1, m below k-1, m=N and N-m below two."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalized-second-difference-bound"),
                DeclarationHandle.Create(Prefix + "normalized_second_difference_bound"),
                H("Uniform bound at every rank from three onward"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every N at least nine, m at most N and rank k with 3 at most k less than N, the same rational second difference is at most 1/(3(k+1)). There is no upper bound on N or k.")),
                    Paragraph(Text("For k at least six, choose(m,k-1) choose(N-m,2) is one nonnegative term of the Vandermonde sum for choose(N,k+1). Thus H is at most 1/choose(k+1,2), which is at most 1/(3(k+1)). For k=3,4,5 the nine-element restriction bounds give respectively 5/63, 1/21 and 1/28; these are at most 1/12, 1/15 and 1/18. The restriction theorem holds for every N at least nine, so the small-rank argument retains the full population range."))),
                DescribeRole.Theorem))));
}
