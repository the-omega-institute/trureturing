using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.WorldModel;

internal sealed class FixedPointStabilityProfileDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/WorldModel/FixedPointStabilityProfile.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform fixed-point stability is a separate multiplier profile whose canonical golden projective radius is positive, strictly below one, and sharper than the ambient stable ratio.",
        H("Fixed Point Stability Profile"),
        Blocks(
            Theorem(
                "uniform-radius-bound-each-attracting",
                "uniform_radius_bound_each_attracting",
                "Uniform Radius Bound Each Attracting",
                "Every coordinate of a uniformly bounded profile is strictly attracting.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "uniform-radius-bound-mono",
                "uniform_radius_bound_mono",
                "Uniform Radius Bound Mono",
                "Enlarging a valid radius below one preserves validity.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-projective-radius-pos",
                "golden_projective_radius_pos",
                "Golden Projective Radius pos",
                "The golden projective radius is positive.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "abs-golden-multiplier-eq-radius",
                "abs_golden_multiplier_eq_radius",
                "Abs Golden Multiplier eq Radius",
                "The absolute golden completion multiplier is exactly its positive radius.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-projective-radius-lt-one",
                "golden_projective_radius_lt_one",
                "Golden Projective Radius lt One",
                "The canonical projective golden system is strictly attracting.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-projective-multiplier-neg",
                "golden_projective_multiplier_neg",
                "Golden Projective Multiplier neg",
                "Its multiplier is negative, recording the alternating side of approach.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-projective-radius-lt-ambient-radius",
                "golden_projective_radius_lt_ambient_radius",
                "Golden Projective Radius lt Ambient Radius",
                "Projective normalization contracts more strongly than the ambient stable ratio φ⁻¹.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-constant-profile-uniform",
                "golden_constant_profile_uniform",
                "Golden Constant Profile Uniform",
                "A world-model family whose every local multiplier is the canonical golden projective multiplier has the exact uniform radius φ⁻².",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-constant-profile-is-uniformly-attracting",
                "golden_constant_profile_is_uniformly_attracting",
                "Golden Constant Profile Is Uniformly Attracting",
                "The canonical golden constant profile is uniformly attracting.",
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
