using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.RefinementClosure;

internal sealed class FiniteHorizonKernelRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ObserverMemory/RefinementClosure/FiniteHorizonKernelRecurrence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-horizon behavior kernels descend by one new coordinate, intersect to the complete kernel, and stabilize at the finite completion depth.",
        H("Finite Horizon Kernel Recurrence"),
        Blocks(
            Theorem(
                "finite-horizon-kernel-succ-iff",
                "finite_horizon_kernel_succ_iff",
                "Finite Horizon Kernel Succ iff",
                "Adding one horizon coordinate intersects the previous kernel with equality of the new terminal observation.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "finite-horizon-kernel-antitone",
                "finite_horizon_kernel_antitone",
                "Finite Horizon Kernel Antitone",
                "Longer observation horizons yield finer kernels.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "complete-kernel-eq-i-inf-finite-horizon",
                "complete_kernel_eq_iInf_finite_horizon",
                "Complete Kernel eq I Inf Finite Horizon",
                "The complete behavior kernel is the infimum of all finite-horizon kernels.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "finite-horizon-first-new-coordinate-strict",
                "finite_horizon_first_new_coordinate_strict",
                "Finite Horizon First New Coordinate Strict",
                "A first separating terminal coordinate certifies strict refinement at the next finite horizon.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "finite-horizon-stabilizes-at-completion-depth",
                "finite_horizon_stabilizes_at_completionDepth",
                "Finite Horizon Stabilizes At Completion Depth",
                "On a finite state space, the canonical completion depth already has the complete infinite-horizon kernel.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."))));

    private static DocumentBlock.Describe Theorem(
        string id,
        string declaration,
        string title,
        string firstParagraph,
        string secondParagraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromLean(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(firstParagraph)),
                Paragraph(Text(secondParagraph))),
            DescribeRole.Theorem);
}
