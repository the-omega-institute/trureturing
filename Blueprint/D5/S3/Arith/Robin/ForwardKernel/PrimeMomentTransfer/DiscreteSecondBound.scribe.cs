using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class DiscreteSecondBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/DiscreteSecondBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Second moment bounds provide the two remaining factors in cubic product replacement.",
        H("Uniform discrete second moments"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("uniform-discrete-second-bound"),
                DeclarationHandle.Create(Prefix + "uniform_discrete_second_bound"),
                H("A uniform variance-size bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume 0<alpha<beta<1/3, M>=1, singular-series values one on empty sets and singletons, MeanSquareHL(3,SS,beta), and IntervalCorrelations(SS). There is C>=0 such that eventually the sum of |S(H,a,b,n)| squared over N<n<=2N is at most C N H log N, uniformly over all natural lengths N^alpha<=H<=N^beta and 0<=a<=b<=M. The second formal overlap value is O(H log N). The quadratic arithmetic error is O(N^(1/2+epsilon) H squared); choosing epsilon below 1/2-beta makes this error at most a constant times N H log N. The resulting estimate is applied to the normalized sampled second moments. Montgomery and Soundararajan, Primes in short intervals (2004), Theorem 3 reaches H<=N^(1/k) for a single interval. The uniform interval and bounded variation weight use here follows from the stated correlation input."))),
                DescribeRole.Theorem))));
}
