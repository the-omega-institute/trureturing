using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.WeylChronology;

internal sealed class GoldenRobustShotComplexityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/WeylChronology/GoldenRobustShotComplexity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive certified robust Ramsey margin gives a positive exponential discrimination rate and an explicit sufficient shot-count inequality for target Bayes risk.",
        H("Golden Robust Shot Complexity"),
        Blocks(
            Paragraph(Text(
                "The sharp affinity-power risk bound is combined with the repository's "
                    + "existing independent-sampling exponential envelope. The resulting "
                    + "shot-rate and logarithmic count condition are deterministic "
                    + "consequences of the previously certified robust margin.")),
            Describe.Lean(
                DescribeId.Create("shot-rate"),
                DeclarationHandle.Create(Prefix + "robustShotRate"),
                H("Robust exponential shot rate"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The rate is one minus the certified one-shot affinity ceiling, namely "
                        + "1-sqrt(1-delta squared)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("margin-le-one"),
                DeclarationHandle.Create(Prefix + "robust_separation_margin_le_one"),
                H("Certified robust margins are bounded by one"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The robust margin is below total variation, while valid finite "
                        + "probability laws have total variation at most one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rate-unit"),
                DeclarationHandle.Create(Prefix + "robust_shot_rate_mem_unit"),
                H("The robust shot rate lies in the unit interval"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A nonnegative certified margin produces a rate between zero and one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rate-positive"),
                DeclarationHandle.Create(Prefix + "robust_shot_rate_pos_of_margin_pos"),
                H("Strict separation gives a positive shot rate"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every strictly positive certified robust margin gives a strictly "
                        + "positive exponential discrimination rate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exponential-error"),
                DeclarationHandle.Create(Prefix + "robust_repeated_optimal_error_le_exponential_rate"),
                H("Repeated risk has an exponential envelope"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The operational finite-suite Bayes risk is bounded by one half of "
                        + "exp(-rate times shots)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("log-budget"),
                DeclarationHandle.Create(Prefix + "robust_repeated_target_error_of_log_budget"),
                H("Logarithmic evidence budget reaches a target risk"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If rate times shots dominates log of one over twice the target risk, "
                        + "the operational repeated error is at most that target."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("shot-count"),
                DeclarationHandle.Create(Prefix + "robust_repeated_target_error_of_shot_count"),
                H("Explicit sufficient shot-count threshold"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a strictly positive robust margin, dividing the logarithmic target "
                        + "budget by the positive shot rate yields a sufficient real-valued "
                        + "lower bound on the number of shots."))),
                DescribeRole.Theorem))));
}
