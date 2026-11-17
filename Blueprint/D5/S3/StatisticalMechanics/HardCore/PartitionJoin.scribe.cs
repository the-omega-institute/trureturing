using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class PartitionJoinDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/HardCore/PartitionJoin.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent subsets of a graph join lie entirely on one side.",
        H("Independent subsets of a graph join"),
        Blocks(
            Describe.Lean(DescribeId.Create("hc-partitionjoin-graph"),
                DeclarationHandle.Create(Prefix + "join"), H("Join of two graphs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The vertex domain is the tagged disjoint sum of the two original domains. "
                    + "Every cross edge is present. Each induced graph retains precisely its original edges. "
                    + "Equivalently, take the complement of the disjoint sum of the two complements."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-partitionjoin-configurations"),
                DeclarationHandle.Create(Prefix + "configurations_join"), H("Complete configuration classification"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For arbitrary finite vertex subsets V and W, the independent subsets of their join "
                    + "are the union of the embedded independent subsets on V and on W. "
                    + "An independent subset containing a left vertex cannot contain a right vertex. "
                    + "Both embedded families contain the empty subset, and their intersection contains nothing else."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-partitionjoin-sum"),
                DeclarationHandle.Create(Prefix + "partition_join"), H("Partition sum with one empty subset"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any activity z in a commutative ring, the native partition sum of the join "
                    + "is the sum of the two native partition sums minus one. Subtracting one corrects "
                    + "the repeated empty subset. This holds for integer polynomials and for complex activities, "
                    + "with no nonzero or positivity hypothesis."))),
                DescribeRole.Theorem))));
}
