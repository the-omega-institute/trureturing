using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenCoding;

internal sealed class GoldenAngleTraceBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/GoldenCoding/GoldenAngleTraceBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rotation trace sends thirty-six degrees to the golden ratio.",
        H("Golden Angle Trace Bridge"),
        Blocks(
            Theorem(
                "thirty-six-degrees-eq-golden-angle",
                "thirty_six_degrees_eq_golden_angle",
                "Thirty Six Degrees eq Golden Angle",
                "Thirty-six degrees is exactly the golden angle in radians.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-angle-trace-eq-golden-ratio",
                "golden_angle_trace_eq_golden_ratio",
                "Golden Angle Trace eq Golden Ratio",
                "The trace of the thirty-six-degree rotation is exactly the golden ratio.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "thirty-six-degree-trace-eq-golden-ratio",
                "thirty_six_degree_trace_eq_golden_ratio",
                "Thirty Six Degree Trace eq Golden Ratio",
                "Degree-valued formulation of the golden trace identity.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "rotation-trace-neg",
                "rotation_trace_neg",
                "Rotation Trace neg",
                "The trace observer forgets orientation.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-angle-ne-neg",
                "golden_angle_ne_neg",
                "Golden Angle ne neg",
                "The golden angle is genuinely distinct from its reflected angle.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "rotation-trace-not-injective",
                "rotation_trace_not_injective",
                "Rotation Trace Not Injective",
                "Consequently the trace observer is not injective.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-angle-trace-quadratic",
                "golden_angle_trace_quadratic",
                "Golden Angle Trace Quadratic",
                "The observed trace retains the golden quadratic relation.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-angle-trace-reciprocal-fixed",
                "golden_angle_trace_reciprocal_fixed",
                "Golden Angle Trace Reciprocal Fixed",
                "The trace also retains the reciprocal fixed-point presentation.",
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
