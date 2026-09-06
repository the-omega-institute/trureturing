using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.WeylChronology;

internal sealed class GoldenRobustFiniteShotDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/WeylChronology/GoldenRobustFiniteShot.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A certified robust Ramsey margin controls the operational finite-shot Bayes risk, with exact transport between recursive iid tests and the Fin-indexed finite-suite representation.",
        H("Golden Robust Finite-Shot Testing"),
        Blocks(
            Paragraph(Text(
                "The module composes the existing calibration margin, robust-law total "
                    + "variation, affinity ceiling, generic finite-suite affinity-product "
                    + "bound and finite-repetition representation equivalence. It introduces "
                    + "no new concentration inequality, classifier, repetition encoding, or "
                    + "Bayes-risk primitive.")),
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
                DescribeId.Create("iid-tv-identity"),
                DeclarationHandle.Create(Prefix + "robust_repeated_optimal_error_eq_iidPower_tv"),
                H("The robust optimum is half one minus recursive iid TV"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For valid robust one-shot laws, the same operational optimum equals one "
                        + "half of one minus total variation of their recursive iidPower "
                        + "laws."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("iid-decision-lower-bound"),
                DeclarationHandle.Create(Prefix + "robust_repeated_optimal_error_le_iid_decision"),
                H("Every recursive iid decision lies above the operational optimum"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every recursive iid decision event transports to a finite-suite decision "
                        + "with identical equal-prior risk, so its risk is at least the existing "
                        + "finiteSuiteOptimalError."))),
                DescribeRole.Theorem),
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
