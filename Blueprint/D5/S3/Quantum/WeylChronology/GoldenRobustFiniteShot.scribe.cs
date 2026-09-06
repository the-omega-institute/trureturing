using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.WeylChronology;

internal sealed class GoldenRobustFiniteShotDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/WeylChronology/GoldenRobustFiniteShot.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A certified robust Ramsey separation margin yields an explicit finite-shot optimal Bayes error upper bound through affinity multiplicativity.",
        H("Golden Robust Finite-Shot Testing"),
        Blocks(
            Paragraph(Text(
                "The module composes the existing calibration margin, robust-law total "
                    + "variation, affinity ceiling, and generic finite-suite affinity-product "
                    + "bound. It introduces no new concentration inequality or classifier.")),
            Describe.Lean(
                DescribeId.Create("repeated-optimal-error"),
                DeclarationHandle.Create(Prefix + "robustRepeatedOptimalError"),
                H("Repeated robust operational risk"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The repeated robust experiment uses the repository's canonical "
                        + "finiteSuiteOptimalError over Fin-N independent Bool coordinates."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("affinity-power"),
                DeclarationHandle.Create(Prefix + "robust_repeated_optimal_error_le_bhattacharyya_power"),
                H("One-shot affinity powers the repeated risk"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For valid one-shot robust probability laws, the optimal repeated "
                        + "equal-prior error is at most one half of the one-shot "
                        + "Bhattacharyya affinity raised to the shot count."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("margin-power"),
                DeclarationHandle.Create(Prefix + "robust_repeated_optimal_error_le_margin_power"),
                H("Certified calibration margin gives a finite-shot risk ceiling"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A nonnegative robust separation margin delta gives the explicit bound "
                        + "e_N^* <= (sqrt(1-delta^2))^N / 2 through the frozen affinity "
                        + "multiplicativity and operational finite-suite owner."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("target-error"),
                DeclarationHandle.Create(Prefix + "robust_repeated_target_error_of_margin_power"),
                H("Robust sufficient shot condition"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If the robust affinity ceiling to the shot count is at most twice a "
                        + "target equal-prior risk, the operational finite-suite optimum "
                        + "reaches that target."))),
                DescribeRole.Theorem))));
}
