using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Queries;

internal sealed class WorldMixedForwardSuffixDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A conditional bound for a suffix selected as a function of the graph world.",
        H("Fresh binary suffixes under a graph prior"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("suffix-weight"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/Queries/WorldMixedForwardSuffix.suffixWeight"),
                H("Weight of a fresh binary suffix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each newly observed position contributes a factor of one half."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-fresh-suffix-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/Queries/WorldMixedForwardSuffix.joint_fresh_suffix_bound"),
                H("Conditioning and mixing fresh suffix bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Draw a world from the prior. At each position in a finite set, the world specifies " +
                        "two distinct choices. Independently of the world and of the other positions, " +
                        "choose a uniform order at each position. Fix a prefix observation. For each world, " +
                        "choose a suffix observation at positions disjoint from the prefix positions.")),
                    Paragraph(Text(
                        "Fix an event of worlds. In every world belonging to that event, suppose the suffix " +
                        "observes at least the stated number of distinct positions. When the prefix has " +
                        "positive mass, the conditional probability of that event and the suffix together " +
                        "is at most the posterior probability of the world event times the corresponding " +
                        "fresh suffix weight. The formal inequality uses extended nonnegative real ratios.")),
                    Paragraph(Text(
                        "In each world, a compatible prefix and suffix satisfy the fixed-world likelihood " +
                        "bound. Incompatible observations contribute zero to the joint event. Sum the " +
                        "worldwise inequalities, weighted by the prior, before dividing by the mass of " +
                        "the prefix."))),
                DescribeRole.Theorem))));
}
