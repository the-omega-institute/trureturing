using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CompletionDynamics.GoldenMobius;

internal sealed class GoldenCrossRatioLinearizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/CompletionDynamics/GoldenMobius/GoldenCrossRatioLinearization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden cross-ratio coordinates exactly linearize the Mobius map.",
        H("Golden Cross Ratio Linearization"),
        Blocks(
            Theorem(
                "golden-cross-ratio-at-golden",
                "golden_cross_ratio_at_golden",
                "Golden Cross Ratio At Golden",
                "This theorem establishes golden cross ratio at golden in the module's typed setting.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-mobius-sub-golden",
                "golden_mobius_sub_golden",
                "Golden Mobius Sub Golden",
                "Numerator identity in a denominator-separated form.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-mobius-sub-conjugate",
                "golden_mobius_sub_conjugate",
                "Golden Mobius Sub Conjugate",
                "Denominator identity in a denominator-separated form.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-cross-ratio-linearization",
                "golden_cross_ratio_linearization",
                "Golden Cross Ratio Linearization",
                "Exact golden projective linearization.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "positive-avoids-golden-singularities",
                "positive_avoids_golden_singularities",
                "Positive Avoids Golden Singularities",
                "Positive points avoid both affine-chart singularities.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-mobius-iterate-pos",
                "golden_mobius_iterate_pos",
                "Golden Mobius Iterate pos",
                "Positivity is invariant under every finite Mobius iterate.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "golden-cross-ratio-iterate",
                "golden_cross_ratio_iterate",
                "Golden Cross Ratio Iterate",
                "Exact geometric contraction law on the positive affine chart.",
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
