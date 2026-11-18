using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class SymmetricTwelveCapacityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric Twelve Capacity", H("Symmetric Twelve Capacity"),
        Blocks(
            Paragraph(Text("Count real incidences between cycle points and all actual lows. On a high twelve-cycle, girth forces a low with two cycle neighbors onto a diameter; adjacent occupied diameters are forbidden, so at most three actual lows are internal. The resulting incidence bound contradicts eight total lows. Finite checks concern only twelve-cycle indices.")),
            Paragraph(Text("This module contributes to the live proof path of SymmetricSliceExclusion.result. Private helper declarations are proof organization and carry no independent novelty claim.")),
            Describe.Lean(
                DescribeId.Create("symmetric-twelve-capacity-incidence-capacity"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwelveCapacity.incidence_capacity"),
                H("incidence capacity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary finite sets and a relation, if every left point has a related right point and each right point has at most two related left points, left cardinality is at most right cardinality plus the number of right points with two related left points."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("symmetric-twelve-capacity-cycle-vertices"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwelveCapacity.cycleVertices"),
                H("cycleVertices"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The image of the twelve indexed cycle points in the actual vertex type."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("symmetric-twelve-capacity-internal-lows"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwelveCapacity.internalLows"),
                H("internalLows"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All actual degree-two vertices with at least two neighbors among those twelve actual cycle points."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("symmetric-twelve-capacity-internal-low-count-le-three"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwelveCapacity.internal_low_count_le_three"),
                H("internal low count le three"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In the actual bipartite graph with degrees two or three, independent lows and girth at least eight, an injective high twelve-cycle of full high degree two has at most three internal actual lows. The parity side hypotheses and all original graph assumptions are retained."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("symmetric-twelve-capacity-cycle-capacity-bound"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwelveCapacity.cycle_capacity_bound"),
                H("cycle capacity bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An injective twelve-point high family with full high degree two needs at least twelve incidences from all actual lows, counted with one extra unit for each internal low. This capacity statement assumes degree two or three and independent lows; it does not add bipartiteness, girth or cycle adjacency."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("symmetric-twelve-capacity-twelve-cycle-impossible"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwelveCapacity.twelve_cycle_impossible"),
                H("twelve cycle impossible"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If exactly eight actual lows coexist with the stated bipartite high twelve-cycle, its internal-low bound and incidence capacity force 12 <= 8 + 3, a contradiction. The exact original hypotheses remain explicit."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricLowPartners"))
        ]));
}
