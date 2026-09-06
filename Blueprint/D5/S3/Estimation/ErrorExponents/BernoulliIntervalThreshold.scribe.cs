using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.ErrorExponents;

internal sealed class BernoulliIntervalThresholdDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Estimation/ErrorExponents/BernoulliIntervalThreshold.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A source-linked control and shared-decision construction with explicit error assumptions.",
        H("BernoulliIntervalThreshold"),
        Blocks(
            Paragraph(Text("The exact statements and proof status are owned by Lean. This is a candidate source without a local compilation verdict, and it does not report a hardware experiment or independent model review.")),
            Describe.Lean(
                DescribeId.Create("thresholdEvent"),
                DeclarationHandle.Create(Prefix + "thresholdEvent"),
                H("thresholdEvent"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same count half-line is used for every allowed parameter pair; ties select the second hypothesis."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("thresholdRisk"),
                DeclarationHandle.Create(Prefix + "thresholdRisk"),
                H("thresholdRisk"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Equal-prior risk of this specified count rule in the existing Binomial measure, not a new optimum."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("kl-lower-endpoint-bound"),
                DeclarationHandle.Create(Prefix + "kl_lower_endpoint_bound"),
                H("kl lower endpoint bound"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A three-point relative-entropy calculation bounds every lower-interval parameter by its nearest endpoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kl-upper-endpoint-bound"),
                DeclarationHandle.Create(Prefix + "kl_upper_endpoint_bound"),
                H("kl upper endpoint bound"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complementation gives the corresponding bound on the upper parameter interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("shared-threshold-error-bounds"),
                DeclarationHandle.Create(Prefix + "shared_threshold_error_bounds"),
                H("shared threshold error bounds"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two errors of the same fixed test obey the imported KL tail inequalities with interval-endpoint rates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-one-test-for-all-parameters"),
                DeclarationHandle.Create(Prefix + "exists_one_test_for_all_parameters"),
                H("exists one test for all parameters"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The event is chosen before the two unknown parameters. This is an actual uniform-test quantifier, not an exchange with pairwise optimization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("thresholdRate"),
                DeclarationHandle.Create(Prefix + "thresholdRate"),
                H("thresholdRate"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The smaller of the two endpoint KL rates is a conservative uniform exponent."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("threshold-rate-pos"),
                DeclarationHandle.Create(Prefix + "threshold_rate_pos"),
                H("threshold rate pos"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Strictly separated intervals and an interior threshold yield a strictly positive rate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("threshold-risk-le-exponential"),
                DeclarationHandle.Create(Prefix + "threshold_risk_le_exponential"),
                H("threshold risk le exponential"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual fixed test has risk at most exp(-N K) throughout the prescribed intervals."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniform-target-error-of-log-budget"),
                DeclarationHandle.Create(Prefix + "uniform_target_error_of_log_budget"),
                H("uniform target error of log budget"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One logarithmic shot budget suffices for the same test and every allowed pair of unknown fixed parameters."))),
                DescribeRole.Theorem))));
}
