using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ZetaCriticalCurvature;

internal sealed class OffLinePairCurvatureKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/ZetaCriticalCurvature/OffLinePairCurvatureKernel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A reflection-paired logarithmic potential has a certified slope whose axis derivative is the off-line curvature dipole.",
        H("Off Line Pair Curvature Kernel"),
        Blocks(
            Theorem(
                "radial-quadratic-has-deriv-at",
                "radial_quadratic_hasDerivAt",
                "Radial Quadratic Has Deriv At",
                "Derivative of the radial quadratic.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "radial-log-potential-has-deriv-at",
                "radial_log_potential_hasDerivAt",
                "Radial Log Potential Has Deriv At",
                "The displayed slope is the ordinary derivative whenever the local factor is nonzero.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "radial-log-slope-has-deriv-at",
                "radial_log_slope_hasDerivAt",
                "Radial Log Slope Has Deriv At",
                "Derivative of the certified slope field.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "radial-quadratic-axis-pos",
                "radial_quadratic_axis_pos",
                "Radial Quadratic Axis pos",
                "Positive displacement keeps both local factors nonzero at the fixed axis.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "off-line-pair-potential-has-deriv-at-axis-zero",
                "off_line_pair_potential_hasDerivAt_axis_zero",
                "Off Line Pair Potential Has Deriv At Axis Zero",
                "The paired potential has zero first normal derivative on the fixed axis.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "off-line-pair-slope-has-deriv-at-axis",
                "off_line_pair_slope_hasDerivAt_axis",
                "Off Line Pair Slope Has Deriv At Axis",
                "The derivative of the certified first-derivative field at the fixed axis is exactly the off-line curvature dipole.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "off-line-pair-curvature-center",
                "off_line_pair_curvature_center",
                "Off Line Pair Curvature Center",
                "Center value of the dipole.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "off-line-pair-curvature-right-zero",
                "off_line_pair_curvature_right_zero",
                "Off Line Pair Curvature Right Zero",
                "Right zero crossing at tangential offset delta.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "off-line-pair-curvature-left-zero",
                "off_line_pair_curvature_left_zero",
                "Off Line Pair Curvature Left Zero",
                "Left zero crossing at tangential offset -delta.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "off-line-pair-curvature-center-neg",
                "off_line_pair_curvature_center_neg",
                "Off Line Pair Curvature Center neg",
                "The center of a genuine off-axis pair is a negative curvature well.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "off-line-pair-curvature-reflection",
                "off_line_pair_curvature_reflection",
                "Off Line Pair Curvature Reflection",
                "The dipole kernel is even in tangential displacement around its center.",
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
