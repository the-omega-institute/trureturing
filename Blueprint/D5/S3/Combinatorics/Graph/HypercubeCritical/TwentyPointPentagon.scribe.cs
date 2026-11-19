using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class TwentyPointPentagonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual matching and complementary pentagons", H("Actual matching and complementary pentagons"),
        Blocks(
            Paragraph(Text("Two compressed five-cycles force every high vertex to have exactly one actual high neighbor. These actual edges define a bijection between the high sides. An edge shared by the two compressed cycles would yield distinct actual three-step paths with common endpoints, contradicting the girth derived from Huang balance. The opposite cycle is therefore the complement of the first five-cycle.")),
            Paragraph(Text("Each actual matching edge has a flip coordinate. On a compressed edge its endpoint matching coordinates are absent from the two-coordinate difference. Applied on both sides, this makes every direction fiber a module of the five-cycle: an outside label is adjacent to all fiber labels or none. The five-cycle has no module of size two, three, or four, so the matching directions are either constant or pairwise distinct. Only subsets of the five labels are checked finitely; cube supports are not enumerated."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointSymmetric")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointGeometry"))
        ]));
}
