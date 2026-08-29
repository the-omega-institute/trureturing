using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeObserver.ProjectiveMemory;

internal sealed class GoldenProjectiveMultiplierDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/PrimeObserver/ProjectiveMemory/GoldenProjectiveMultiplier.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The conjugate golden mode scales by minus the inverse golden ratio, while its ratio to the dominant mode scales by its inverse square.",
        H("Golden Projective Multiplier"),
        Blocks(
            Theorem(
                "golden-conjugate-eq-neg-inv",
                "golden_conjugate_eq_neg_inv",
                "Golden Conjugate eq neg Inv",
                "The ambient stable eigenvalue is minus the inverse golden ratio.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "stable-dominant-ratio-eq-projective-multiplier",
                "stable_dominant_ratio_eq_projective_multiplier",
                "Stable Dominant Ratio eq Projective Multiplier",
                "The ratio of stable and dominant eigenvalues is the exact projective completion multiplier.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "projective-defect-modal-step",
                "projective_defect_modal_step",
                "Projective Defect Modal Step",
                "One Fibonacci modal step multiplies the normalized defect by the projective multiplier.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "projective-multiplier-of-modal-laws",
                "projective_multiplier_of_modal_laws",
                "Projective Multiplier Of Modal Laws",
                "Abstract recurrence form: ambient laws A' = φA and D' = ψD imply the projective law whenever the dominant coordinate is nonzero.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "forced-projective-step-zero",
                "forced_projective_step_zero",
                "Forced Projective Step Zero",
                "This theorem establishes forced projective step zero in the module's typed setting.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "zero-state-zero-forcing",
                "zero_state_zero_forcing",
                "Zero State Zero Forcing",
                "A vanishing state with zero forcing remains zero in one step.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "ambient-and-projective-multipliers-ne",
                "ambient_and_projective_multipliers_ne",
                "Ambient And Projective Multipliers ne",
                "The ambient stable eigenvalue and projective multiplier encode different normalization levels.",
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
