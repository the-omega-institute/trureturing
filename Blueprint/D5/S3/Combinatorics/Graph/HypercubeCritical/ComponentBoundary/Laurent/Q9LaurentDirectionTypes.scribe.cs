using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent;

internal sealed class Q9LaurentDirectionTypesDocument : IScribeDocumentDefinition
{
    private const string Boundary =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/";
    private const string Owner = Boundary + "Laurent/Q9LaurentDirectionTypes.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Connectedness restricts the possible numbers of distinct Laurent direction triples.",
        H("A gap in Laurent direction types"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("q9-laurent-direction-type-gap"),
                DeclarationHandle.Create(Owner + "card_directionTypes_le_three_or_eq_five_or_ge_seven"),
                H("Four and six direction triples are impossible"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A two-step walk preserves the direction triple of its middle vertex. Thus a change of neighbor partition along the walk gives two distinct partitions sharing a block. Their union has five triples. The two different splits of the complementary six axes force any third partition to contribute at least two new triples."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("q9-laurent-five-type-common-block"),
                DeclarationHandle.Create(Owner + "two_partitions_of_five_directionTypes"),
                H("Five triples force a common direction block"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exactly five triples leave two realized neighbor partitions. They share one block. Deleting that block from a partition leaves a split of the complementary six coordinates into two triples."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(Boundary + "Q9LaurentGainPartition"))]));
}
