using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaCompletionFlow;

internal sealed class NewtonCompletionFieldDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/ZetaCompletionFlow/NewtonCompletionField.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Newton completion vector is scale invariant, detects roots under a regular derivative, and exactly completes affine zero models in one step.",
        H("Newton Completion Field"),
        Blocks(
            Theorem(
                "newton-completion-vector-eq-zero-iff",
                "newton_completion_vector_eq_zero_iff",
                "Newton Completion Vector eq Zero iff",
                "At a regular point, the Newton vector vanishes exactly at a root.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "newton-completion-vector-scale-invariant",
                "newton_completion_vector_scale_invariant",
                "Newton Completion Vector Scale Invariant",
                "Common nonzero rescaling of a function and its derivative field leaves the Newton vector unchanged.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "affine-newton-completion-vector",
                "affine_newton_completion_vector",
                "Affine Newton Completion Vector",
                "The Newton vector of an affine simple-zero model points exactly from the current point to its root.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "affine-newton-completion-step",
                "affine_newton_completion_step",
                "Affine Newton Completion Step",
                "Consequently, an affine simple-zero model completes in one Newton step.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "root-fixed-by-newton-completion",
                "root_fixed_by_newton_completion",
                "Root Fixed By Newton Completion",
                "A genuine regular root is fixed by the Newton completion step.",
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
