using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.ErrorExponents;

internal sealed class FiniteSuiteAffinityProductBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Estimation/ErrorExponents/FiniteSuiteAffinityProductBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Optimal equal-prior error of a finite independent suite is at most one half of the product of its coordinate Bhattacharyya affinities, including zero-affinity endpoints.",
        H("Finite-Suite Affinity Product Bound"),
        Blocks(
            Paragraph(Text(
                "This module composes the existing zero-aware extended finite-suite error "
                    + "squeeze with the frozen exact Bhattacharyya multiplicativity of "
                    + "windowLaw. It introduces no new product law, testing inequality, or "
                    + "decision rule.")),
            Describe.Lean(
                DescribeId.Create("budget-decay-joint-affinity"),
                DeclarationHandle.Create(Prefix + "finite_suite_budget_decay_eq_joint_affinity"),
                H("Extended budget decay is the joint affinity"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The zero-aware extended Bhattacharyya budget decays back to the exact "
                        + "joint-law affinity, including the zero-affinity endpoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("optimal-error-product-bound"),
                DeclarationHandle.Create(Prefix + "finite_suite_optimal_error_le_bhattacharyya_product"),
                H("Optimal error is bounded by the affinity product"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For normalized nonnegative coordinate laws, the operational finite-suite "
                        + "equal-prior optimum is at most one half of the product of the "
                        + "coordinate Bhattacharyya affinities. No positivity premise on those "
                        + "affinities is required."))),
                DescribeRole.Theorem))));
}
