using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Queries;

internal sealed class ForwardSuffixLawDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditioning on observed binary slots leaves distinct unused positions uniform.",
        H("The likelihood of fresh binary slots"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("suffix-after-prefix"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/Queries/ForwardSuffixLaw.suffix_after_prefix"),
                H("One factor of one half for each newly observed position"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take a finite set of positions with two distinct available values "
                        + "at each position. Draw independently uniform orders of their two "
                        + "slots. Fix an earlier observation and a later observation, each "
                        + "specifying values at any subset of slots. The positions with "
                        + "at least one specified slot in the two observations are disjoint.")),
                    Paragraph(Text(
                        "Assume the earlier observation is compatible with the available "
                        + "values and the two-slot distinctness condition. Given that "
                        + "observation, a compatible later observation has probability two "
                        + "to the minus number of its observed positions. An incompatible "
                        + "later observation has probability zero.")),
                    Paragraph(Text(
                        "A table matches both observations exactly when it matches their "
                        + "union. Compatibility of the union is equivalent to the two "
                        + "separate compatibility conditions. The visited positions of the "
                        + "union are a disjoint union, so the power of two for the earlier "
                        + "positions cancels in the conditional ratio."))),
                DescribeRole.Theorem))));
}
