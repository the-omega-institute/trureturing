using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class WeightedIntegralToolsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/WeightedIntegralTools.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform integration bounds for bounded variation weights.",
        H("Weighted integral tools"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bv-sup-bound"),
                DeclarationHandle.Create(Prefix + "bv_sup_bound"),
                H("Supremum bound for a BV weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If the supremum bound plus the total variation of a supported weight is at most B, then its absolute value is at most B at every real argument."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-integral-uniform-bound"),
                DeclarationHandle.Create(Prefix + "weighted_integral_uniform_bound"),
                H("A uniform weighted integral bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For nonnegative N, B and E, if the absolute values of w(x/N) and f(x) on [N,2N] are at most B and E respectively, then the absolute value of their product integral is at most N B E."))),
                DescribeRole.Theorem))));
}
