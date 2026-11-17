using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class RealLengthTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/RealLengthTransfer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact physical endpoint rescaling transfers integer-length mixed moments to all real lengths.",
        H("Real-length continuous mixed moments"),
        Blocks(
            Paragraph(Text(
                "Montgomery and Soundararajan, Primes in short intervals, Communications in Mathematical Physics "
                + "252 (2004), 589–617, Theorem 3, reaches H<=N^(1/k) for a single interval's kth moment "
                + "under the corresponding correlation errors. The endpoint-uniform overlapping-interval, "
                + "BV-weighted, continuously sampled cubic conclusion on beta<1/3 is repo-derived. "
                + "Its sampling argument uses a pointwise increment discrepancy and uniform second moments; "
                + "the fourth-order branch retains beta<1/4 and the four-point hypothesis.")),
            Describe.Lean(
                DescribeId.Create("real-third"),
                DeclarationHandle.Create(Prefix + "real_third"),
                H("Real-length cubic moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume 0<alpha<beta<1/3, the empty and singleton normalizations of the singular series, MeanSquareHL(3,SS,beta), and the interval correlation input. For M>=1 and every delta>0, the absolute continuous cubic mixed moment is eventually at most B*delta uniformly for real N^alpha<=H<=N^beta, intervals in [0,M], and weights supported on [1,2] with supremum-plus-variation bound B (BVBound(w,B))."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("real-fourth"),
                DeclarationHandle.Create(Prefix + "real_fourth"),
                H("Real-length fourth moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under 0<alpha<beta<1/4 and MeanSquareHL4(SS,beta), together with the same normalizations and interval correlations, the continuous fourth mixed moment for real lengths equals the weight integral times kappa(N,H)^2 times the fourth overlap pairing, up to an error uniformly at most B*delta. Rescaling endpoints from H to its floor produces exactly cancelling fourth-order normalizer and overlap factors; the remaining variance ratio difference tends uniformly to zero."))),
                DescribeRole.Theorem))));
}
