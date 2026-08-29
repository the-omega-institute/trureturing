using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaCompletionFlow;

internal sealed class SimpleZeroCompletionVelocityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/ZetaCompletionFlow/SimpleZeroCompletionVelocity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nondegenerate zero-thread chain equation determines its completion velocity by the ratio of completion and state derivatives.",
        H("Simple Zero Completion Velocity"),
        Blocks(
            Theorem(
                "zero-completion-velocity-eq-of-chain",
                "zero_completion_velocity_eq_of_chain",
                "Zero Completion Velocity eq Of Chain",
                "Algebraic extraction of the simple-zero completion velocity from the chain rule identity.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "zero-completion-velocity-satisfies-chain",
                "zero_completion_velocity_satisfies_chain",
                "Zero Completion Velocity Satisfies Chain",
                "Substitution back into the chain equation.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "zero-completion-velocity-scale-invariant",
                "zero_completion_velocity_scale_invariant",
                "Zero Completion Velocity Scale Invariant",
                "Common nonzero rescaling of the analytic family leaves zero velocity unchanged.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "zero-completion-velocity-eq-zero-iff",
                "zero_completion_velocity_eq_zero_iff",
                "Zero Completion Velocity eq Zero iff",
                "At a simple zero, vanishing completion velocity is equivalent to vanishing completion-direction forcing.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "zero-completion-velocity-ne-zero",
                "zero_completion_velocity_ne_zero",
                "Zero Completion Velocity ne Zero",
                "A nonzero forcing term yields a nonzero velocity at a simple zero.",
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
