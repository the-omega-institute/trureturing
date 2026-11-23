using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Marginals;

internal sealed class BinaryDeletionGrowthDocument : IScribeDocumentDefinition
{
    private const string Dimension =
        "D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionGrowth.kernelDimension_lower";
    private const string Ratio =
        "D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionGrowth.kernelDimension_to_allowedCount";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Growth of the one-site deletion kernel on open chains with forbidden occupied runs.",
        H("Exponential growth of the binary deletion kernel"),
        Blocks(
            Describe.Lean(DescribeId.Create("binary-deletion-kernel-growth"),
                DeclarationHandle.Create(Dimension), H("Uniform lower bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Consider a chain of k plus two sites that forbids a run of length K. "
                    + "When K is at least four, the dimension of the supported "
                    + "one-site deletion kernel is at least (100/43) to the power k. "
                    + "The bound also holds when the forbidden run is longer "
                    + "than the chain.")),
                    Paragraph(Text(
                    "Begin with two opposite differences. Track the ages of the last "
                    + "occurrences of the two orientations. The six states have two "
                    + "distinct ages between zero and three. A move repeats the newer "
                    + "orientation, emits the older orientation, or adds agreement. "
                    + "Every permitted move keeps both ages below four. The resulting "
                    + "patterns contain both orientations in each window of four, "
                    + "and hence in each longer window.")),
                    Paragraph(Text(
                    "Weight the states with ages (0,1), (0,2), (0,3), (1,2), (1,3), "
                    + "and (2,3) by 100, 75, 43, 58, 32, and 18 respectively. At each "
                    + "state the sum of successor weights is at least 100/43 times its "
                    + "weight. Induction on the number of remaining moves gives the "
                    + "lower bound from the initial state, whose weight is 100. Each "
                    + "valid output encodes its moves uniquely."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("binary-deletion-kernel-relative-growth"),
                DeclarationHandle.Create(Ratio), H("Growth relative to the allowed space"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Consider k plus two sites and forbid an occupied run of length K, with K at "
                    + "least four. The number of allowed words is positive because the all-zero word "
                    + "is allowed. There are at most 2^(k+2) words. "
                    + "Dividing the kernel lower bound by this upper bound shows that "
                    + "the ratio of the kernel dimension to the number of allowed words "
                    + "is at least one quarter of (50/43) to the power k."))),
                DescribeRole.Theorem))));
}
