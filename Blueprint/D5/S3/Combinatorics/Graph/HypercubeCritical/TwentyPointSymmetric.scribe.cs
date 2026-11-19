using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class TwentyPointSymmetricDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Twenty Point Symmetric", H("Twenty Point Symmetric"),
        Blocks(
            Paragraph(Text("Private proof organization for the symmetric 10/10 parity branch of the actual twenty-point slice. Actual low-path incidence counting identifies the number of compressed edges with the number of opposite degree-two vertices, so each auxiliary graph has five vertices and five edges.")),
            Paragraph(Text("The degree identity bounds compressed degrees by three. The degree sum gives either a two-regular graph, which is a five-cycle, or a degree-three vertex. In the latter case triangle exclusion and the five-vertex cardinality force a four-cycle with one leaf, with exact neighbor tables. The classification uses actual degree and incidence arguments, without enumerating supports or subgraphs.")),
            Paragraph(Text("A mixed pair is impossible: the leaf has two actual high neighbors on the opposite side, but every pair in a five-cycle is adjacent or has a common neighbor, contradicting actual short-path uniqueness. The remaining alternatives are two five-cycles or two four-cycles with leaves. Their actual Huang-sign exclusions remain necessary for the complete obstruction."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointTheta")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/Brooks/General"))
        ]));
}
