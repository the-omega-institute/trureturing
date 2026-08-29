using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CompletionDynamics.GoldenMobius;

internal sealed class GoldenMobiusMapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/CompletionDynamics/GoldenMobius/GoldenMobiusMap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reciprocal golden Mobius map has the golden ratio and its conjugate as fixed points and preserves the positive half-line.",
        H("Golden Mobius Map"),
        Blocks(
            Theorem(
                "golden-mobius-fixed-golden",
                "golden_mobius_fixed_golden",
                "Golden Mobius Fixed Golden",
                "The positive golden root is a fixed point.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-mobius-fixed-conjugate",
                "golden_mobius_fixed_conjugate",
                "Golden Mobius Fixed Conjugate",
                "The negative conjugate golden root is the second fixed point.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-fixed-points-ne",
                "golden_fixed_points_ne",
                "Golden Fixed Points ne",
                "The two fixed points are distinct.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-fixed-point-gap",
                "golden_fixed_point_gap",
                "Golden Fixed Point Gap",
                "Their oriented gap is the square root of the discriminant.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-mobius-pos",
                "golden_mobius_pos",
                "Golden Mobius pos",
                "Positive starting points remain in the positive affine chart.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-projective-multiplier-eq-neg-conjugate-sq",
                "golden_projective_multiplier_eq_neg_conjugate_sq",
                "Golden Projective Multiplier eq neg Conjugate Sq",
                "The projective multiplier can equivalently be read from the stable golden conjugate eigenvalue.",
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
