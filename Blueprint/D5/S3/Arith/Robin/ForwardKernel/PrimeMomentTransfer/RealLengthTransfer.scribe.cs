using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class RealLengthTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/RealLengthTransfer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact physical endpoint rescaling transfers integer-length mixed moments to all real lengths.",
        H("Real-length continuous mixed moments"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("real-third"),
                DeclarationHandle.Create(Prefix + "real_third"),
                H("Real-length cubic moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume 0<alpha<beta<1/4, the empty and singleton normalizations of the singular series, MeanSquareHL4(SS,beta), and the interval correlation input. For M>=1 and every delta>0, the absolute continuous cubic mixed moment is eventually at most B*delta uniformly for real N^alpha<=H<=N^beta, intervals in [0,M], and weights supported on [1,2] with supremum-plus-variation bound B (BVBound(w,B))."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("real-fourth"),
                DeclarationHandle.Create(Prefix + "real_fourth"),
                H("Real-length fourth moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "With these same hypotheses, the continuous fourth mixed moment for real lengths equals the weight integral times kappa(N,H)^2 times the fourth overlap pairing, up to an error uniformly at most B*delta. Rescaling endpoints from H to its floor produces exactly cancelling fourth-order normalizer and overlap factors; the remaining variance ratio difference tends uniformly to zero."))),
                DescribeRole.Theorem))));
}
