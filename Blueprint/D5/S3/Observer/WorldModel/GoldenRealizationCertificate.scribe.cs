using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.WorldModel;

internal sealed class GoldenRealizationCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/WorldModel/GoldenRealizationCertificate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One certificate packages the quadratic, Fibonacci, rotation-trace, Mobius-fixed, and projective-attraction realizations of the golden structure while exhibiting a repelling countermodel.",
        H("Golden Realization Certificate"),
        Blocks(
            Theorem(
                "canonical-golden-cross-representation-certificate",
                "canonical_golden_cross_representation_certificate",
                "Canonical Golden Cross Representation Certificate",
                "The canonical golden structure satisfies the full cross-representation certificate.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-repelling-affine-fixed",
                "golden_repelling_affine_fixed",
                "Golden Repelling Affine Fixed",
                "The same golden point can be fixed in a different dynamical system.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-repelling-affine-has-deriv-at",
                "golden_repelling_affine_hasDerivAt",
                "Golden Repelling Affine Has Deriv At",
                "The affine countermodel has derivative φ² at the fixed point.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-repelling-affine-multiplier-gt-one",
                "golden_repelling_affine_multiplier_gt_one",
                "Golden Repelling Affine Multiplier Gt One",
                "The affine countermodel is strictly repelling.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-fixed-does-not-force-attraction",
                "golden_fixed_does_not_force_attraction",
                "Golden Fixed Does Not Force Attraction",
                "Hence fixedness of the golden point alone does not imply attraction.",
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
