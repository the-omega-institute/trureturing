using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CompletionDynamics.GoldenMobius;

internal sealed class GoldenProjectiveDerivativeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/CompletionDynamics/GoldenMobius/GoldenProjectiveDerivative.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden Mobius derivative equals its projective multiplier.",
        H("Golden Projective Derivative"),
        Blocks(
            Theorem(
                "golden-mobius-has-deriv-at",
                "golden_mobius_hasDerivAt",
                "Golden Mobius Has Deriv At",
                "Ordinary differentiation gives the same multiplier as exact projective linearization.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "deriv-golden-mobius-at-golden",
                "deriv_golden_mobius_at_golden",
                "Deriv Golden Mobius At Golden",
                "Evaluation of deriv at the golden fixed point.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "abs-golden-projective-multiplier",
                "abs_golden_projective_multiplier",
                "Abs Golden Projective Multiplier",
                "The projective multiplier has the expected positive magnitude.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "abs-golden-projective-multiplier-lt-one",
                "abs_golden_projective_multiplier_lt_one",
                "Abs Golden Projective Multiplier lt One",
                "The completion derivative is a strict contraction in projective coordinates.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "linearized-golden-has-deriv-at-zero",
                "linearized_golden_hasDerivAt_zero",
                "Linearized Golden Has Deriv At Zero",
                "Multiplication by the golden multiplier has that derivative at zero.",
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
