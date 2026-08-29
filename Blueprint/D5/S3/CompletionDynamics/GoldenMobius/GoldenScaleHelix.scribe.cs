using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CompletionDynamics.GoldenMobius;

internal sealed class GoldenScaleHelixDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/CompletionDynamics/GoldenMobius/GoldenScaleHelix.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden completion lifts to a helix whose deck step advances one scale period and reverses orientation.",
        H("Golden Scale Helix"),
        Blocks(
            Theorem(
                "golden-scale-period-pos",
                "golden_scale_period_pos",
                "Golden Scale Period pos",
                "The golden logarithmic scale period is strictly positive.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-scale-period-eq-neg-log-multiplier",
                "golden_scale_period_eq_neg_log_multiplier",
                "Golden Scale Period eq neg Log Multiplier",
                "The logarithmic scale period is exactly the negative logarithm of the absolute golden projective multiplier.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-helix-step-level",
                "goldenHelixStep_level",
                "Golden Helix Step Level",
                "This theorem establishes golden helix step level in the module's typed setting.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-helix-step-scale-lift",
                "goldenHelixStep_scaleLift",
                "Golden Helix Step Scale Lift",
                "This theorem establishes golden helix step scale lift in the module's typed setting.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-helix-step-orientation",
                "goldenHelixStep_orientation",
                "Golden Helix Step Orientation",
                "This theorem establishes golden helix step orientation in the module's typed setting.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-helix-step-twice-orientation",
                "goldenHelixStep_twice_orientation",
                "Golden Helix Step Twice Orientation",
                "Two completion turns restore the orientation sheet.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-helix-step-twice-scale-lift",
                "goldenHelixStep_twice_scaleLift",
                "Golden Helix Step Twice Scale Lift",
                "Two completion turns add exactly two golden scale periods.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-helix-step-scale-lift-strict",
                "goldenHelixStep_scaleLift_strict",
                "Golden Helix Step Scale Lift Strict",
                "Every completion turn strictly increases the lifted scale coordinate.",
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
