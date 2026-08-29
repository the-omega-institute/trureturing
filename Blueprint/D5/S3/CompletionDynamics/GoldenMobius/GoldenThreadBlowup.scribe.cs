using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CompletionDynamics.GoldenMobius;

internal sealed class GoldenThreadBlowupDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/CompletionDynamics/GoldenMobius/GoldenThreadBlowup.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden completion curves share the same completed value while their first blow-up coordinate and tangent retain the observer origin.",
        H("Golden Thread Blowup"),
        Blocks(
            Theorem(
                "golden-thread-curve-zero",
                "golden_thread_curve_zero",
                "Golden Thread Curve Zero",
                "This theorem establishes golden thread curve zero in the module's typed setting.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-thread-curve-sub-golden",
                "golden_thread_curve_sub_golden",
                "Golden Thread Curve Sub Golden",
                "Difference from the completed fixed point in the inverse projective chart.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-thread-curve-sub-conjugate",
                "golden_thread_curve_sub_conjugate",
                "Golden Thread Curve Sub Conjugate",
                "Difference from the conjugate fixed point in the inverse projective chart.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-cross-ratio-thread-curve",
                "golden_cross_ratio_thread_curve",
                "Golden Cross Ratio Thread Curve",
                "The inverse chart recovers the prescribed projective coordinate exactly.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-thread-curve-has-deriv-at",
                "golden_thread_curve_hasDerivAt",
                "Golden Thread Curve Has Deriv At",
                "The inverse golden chart has first derivative c(φ-ψ) at completion.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-thread-curve-has-deriv-at-sqrt-five",
                "golden_thread_curve_hasDerivAt_sqrt_five",
                "Golden Thread Curve Has Deriv At Sqrt Five",
                "The tangent coefficient displays the discriminant gap sqrt 5.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-thread-completion-value-eq",
                "golden_thread_completion_value_eq",
                "Golden Thread Completion Value eq",
                "Two origin coefficients give the same completed value.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-thread-tangent-injective",
                "golden_thread_tangent_injective",
                "Golden Thread Tangent Injective",
                "Distinct origin coefficients give distinct completion tangents.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-geometric-thread-cross-ratio",
                "golden_geometric_thread_cross_ratio",
                "Golden Geometric Thread Cross Ratio",
                "At any depth where the inverse affine chart is defined, the blow-up coordinate is exactly c * multiplier^n.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-geometric-thread-origin-recovery",
                "golden_geometric_thread_origin_recovery",
                "Golden Geometric Thread Origin Recovery",
                "Since the multiplier is nonzero, renormalization recovers the origin coefficient at every finite depth.",
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
