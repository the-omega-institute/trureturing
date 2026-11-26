using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9DistanceThreeCrossingCountDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9DistanceThreeCrossingCount.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unshared distance-three contacts force at least 45 active rows per side and 162 crossing edges.",
        H("Shortest paths through the two exteriors"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("active-card-and-crossing-darts"),
                DeclarationHandle.Create(Owner + "active_card_and_crossing_darts"),
                H("Active vertices and crossing edges"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume balanced induced cubic supports at mutual separation at least three, with a "
                    + "distance-three contact and disjoint occupied directions at every such contact. "
                    + "Assume also two support neighbors at each active exterior vertex. Each side has at "
                    + "least 18 closest endpoints and each endpoint reaches at least five active vertices. "
                    + "Counting these incidences forces 45 active vertices per side. Each closest endpoint "
                    + "has at least six contact triples. Each closest pair gives six shortest paths, while "
                    + "each crossing edge can serve as the middle edge of at most four of them. This forces "
                    + "162 crossing edges."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9DistanceThreeActiveBoundary")),
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9MinimumContactDirectionChart"))
        ]));
}
