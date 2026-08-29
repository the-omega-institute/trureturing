using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CompletionDynamics.ObserverJet;

internal sealed class PairedOddJetCancellationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/CompletionDynamics/ObserverJet/PairedOddJetCancellation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reflection pairing cancels odd linear jets while preserving quadratic information in the even channel.",
        H("Paired Odd Jet Cancellation"),
        Blocks(
            Theorem(
                "even-add-odd-eq",
                "even_add_odd_eq",
                "Even Add Odd eq",
                "Every profile decomposes exactly into its paired even and odd channels.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "even-channel-neg",
                "even_channel_neg",
                "Even Channel neg",
                "The paired even channel is invariant under reflection.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "odd-channel-neg",
                "odd_channel_neg",
                "Odd Channel neg",
                "The paired odd channel changes sign under reflection.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "linear-jet-even-channel-zero",
                "linear_jet_even_channel_zero",
                "Linear Jet Even Channel Zero",
                "A first-order signed jet vanishes after pairing in the even channel.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "linear-jet-odd-channel",
                "linear_jet_odd_channel",
                "Linear Jet Odd Channel",
                "The same first-order jet is retained exactly in the odd channel.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "reflected-tangent-square",
                "reflected_tangent_square",
                "Reflected Tangent Square",
                "Squaring a reflected tangent removes its sign.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "quadratic-jet-even-channel",
                "quadratic_jet_even_channel",
                "Quadratic Jet Even Channel",
                "A quadratic jet survives reflection pairing in the even channel.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "quadratic-jet-odd-channel-zero",
                "quadratic_jet_odd_channel_zero",
                "Quadratic Jet Odd Channel Zero",
                "A quadratic jet has zero odd component.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "paired-tangent-average-zero",
                "paired_tangent_average_zero",
                "Paired Tangent Average Zero",
                "Direct vector-pair version of first-order cancellation.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "paired-tangent-second-moment",
                "paired_tangent_second_moment",
                "Paired Tangent Second Moment",
                "The second moment of a reflected tangent pair is the original square.",
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
