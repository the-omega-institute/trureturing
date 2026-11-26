using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LinearForests;

internal sealed class AlternatingSuccessorSetBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A contracted cycle count bounds the probability of a set of possible successors.",
        H("Successor sets in compatible single cycles"),
        Blocks(Describe.Lean(
            DescribeId.Create("compatible-cycle-successor-set-mass"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/Graph/LinearForests/AlternatingSuccessorSetBound.successor_set_mass_le"),
            H("Probability bound for a set of compatible successors"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Give each label a source and a destination color, each taking one of two values. "
                + "Sample uniformly among single cycles on the finite label set in which each "
                + "label's destination color equals its successor's source color. Assume both "
                + "source colors occur at least twice. For a specified label and a target set "
                + "excluding that label, the probability that its successor belongs to the "
                + "target set is at most the target set's size divided by one less than the "
                + "number of labels whose source color matches the specified destination color."))),
            DescribeRole.Theorem))));
}
