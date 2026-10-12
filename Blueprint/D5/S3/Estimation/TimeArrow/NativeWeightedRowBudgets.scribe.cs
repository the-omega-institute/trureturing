using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.TimeArrow;

internal sealed class NativeWeightedRowBudgetsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original row-count law controls full weighted sums after the count cut is restored. An environment anchor estimate allows the good event to vary inside an observation fiber.",
        H("Native row tails, moments, and environment anchors"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("native-row-count-tail"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeWeightedRowBudgets.NativeRowCountTail.native_row_count_tail"),
                H("Native row count tail"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The pair and path experiments satisfy the same exponential bound for a single row outside the count cut."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-all-row-count-cut"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeWeightedRowBudgets.NativeRowCountTail.native_all_row_count_cut"),
                H("Native all row count cut"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Summing the single-row estimate bounds the probability that any row leaves the count cut."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-truncated-weighted-moments"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeWeightedRowBudgets.NativeRowMomentTransfer.native_truncated_weighted_moments"),
                H("Native truncated weighted moments"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One-row and two-row relative point estimates control the mean and second moment of finite weighted count sums."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-full-weighted-moments"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeWeightedRowBudgets.NativeWeightedRowBudgets.native_full_weighted_moments"),
                H("Native full weighted moments"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complete weighted sum retains the displayed mean and second-moment estimates after its reference and actual count tails are restored."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-full-weighted-deviation"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeWeightedRowBudgets.NativeWeightedRowBudgets.native_full_weighted_deviation"),
                H("Native full weighted deviation"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The full second-moment estimate yields a probability bound for deviation from the complete reference mean."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-environment-anchor-budget"),
                DeclarationHandle.Create("D5/S3/Estimation/TimeArrow/NativeWeightedRowBudgets.NativeEnvironmentAnchors.finite_environment_anchor_budget"),
                H("Finite environment anchor budget"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A fiberwise bound on the central-event complement controls all environments without a good central anchor, even when the good event is not constant on fibers."))),
                DescribeRole.Theorem)
        )));
}
