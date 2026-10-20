using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.KyFanGap;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Infinitely many graph Ky Fan prefixes have strict asymptotic gaps.",
        H("The asymptotic graph Ky Fan conjecture"), Blocks(
            Describe.Lean(DescribeId.Create("nikiforov-kyfan-gap-result"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/KyFanGap/Result.result"),
                H("Infinitely many strict gaps"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Eigenstructure/nikiforov2015extrema")),
                Blocks(Paragraph(Text("For infinitely many natural numbers k, the maximum Ky Fan k-sum over simple graphs on n vertices, divided by n, converges as n tends to infinity to a value strictly below (1+sqrt(k))/2. The Ky Fan sum uses decreasing singular values, including the absolute values of negative eigenvalues. The finite graph maximum ranges over every graph on Fin n, and the pinned definition extends the sum by zero singular values beyond the dimension.")),
                    Paragraph(Text("Every positive nonsquare k has a uniform positive gap for all symmetric zero-one matrices of order at least k. Hence its graph maxima eventually obey the same bound. Blow-ups and padding give convergence to the explicit supremum of xi(k,m+k)/(m+k) over natural m. The limit is at most the universal bound minus the positive gap. Infinitely many primes supply infinitely many positive nonsquare k. The uniform gap holds for every positive nonsquare prefix; the final infinitude proof uses the prime subset. No effective value or optimal size of the gap is claimed."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("nikiforov-2015-ky-fan-asymptotic-gap"),
                    ResolutionKind.Proved)))));
}
