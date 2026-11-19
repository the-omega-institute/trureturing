using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class CutoffWeightsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CutoffWeights.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Closed interval cutoffs give bounded variation weights for dyadic moments.",
        H("Cutoff weights"),
        Blocks(
            Describe.Lean(DescribeId.Create("cutoff-bv"), DeclarationHandle.Create(Prefix + "cutoff_bv"), H("Indicator cutoff bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For 1 <= u <= v <= 2, the indicator of the closed interval [u,v] vanishes outside [1,2], has supremum at most one, and has total variation at most two. Its supremum bound plus total variation is at most three, also when u=v."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("log-block-bv"), DeclarationHandle.Create(Prefix + "log_block_bv"), H("Logarithmic block weight bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For 1 <= u <= v <= 2, extend 1/(t log 2) by zero outside the closed interval [u,v]. The resulting function vanishes outside [1,2], has supremum at most 1/log 2 and total variation at most 2/log 2. Their sum is at most 3/log 2, including a single-point interval."))), DescribeRole.Theorem))));
}
