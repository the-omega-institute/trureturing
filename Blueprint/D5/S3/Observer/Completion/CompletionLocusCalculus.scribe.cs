using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Completion;

internal sealed class CompletionLocusCalculusDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Completion/CompletionLocusCalculus.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Structural completion loci compose by intersection, pull back along arbitrary parameter maps, and retain gauge stability under conjunction.",
        H("Completion Locus Calculus"),
        Blocks(
            Theorem(
                "completion-locus-pair-eq-inter",
                "completion_locus_pair_eq_inter",
                "Completion Locus Pair eq Inter",
                "Conjoining two normalizations and pairing their defects gives exactly the intersection of their completion loci.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "completion-locus-preimage",
                "completion_locus_preimage",
                "Completion Locus Preimage",
                "Completion loci pull back exactly along arbitrary parameter maps.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "completion-locus-intersection-gauge-stable",
                "completion_locus_intersection_gauge_stable",
                "Completion Locus Intersection Gauge Stable",
                "If two completion loci are stable under the same gauge action, their conjoined locus is stable as well.",
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
