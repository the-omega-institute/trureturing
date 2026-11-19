using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class TwentyPointThetaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Twenty Point Theta", H("Twenty Point Theta"),
        Blocks(
            Paragraph(Text("This private proof unit derives the seven-high-vertex theta incidence in the 11/9 parity branch of the actual twenty-point slice. Its inputs are actual bipartition, degrees two or three, independent lows, girth at least eight, three high vertices on one side, seven on the other, and two low vertices on the nine-point side.")),
            Paragraph(Text("The five actual high-high edges have distinct endpoints on the seven-point side. The central endpoint has two compressed neighbors with no actual high neighbor. Actual short-path uniqueness separates each pair of high neighbors of the other two roots. The degree identities and triangle exclusion then force the theta paths P–Z–Q, P–A–B–Q, and P–C–D–Q, with actual high-high edges uA, uD, vZ, wB, and wC. The seven compressed vertices are proved distinct.")),
            Paragraph(Text("The argument follows the local twenty-point reduction for the Hong–Wu–Xia Section 7 Problem 2 branch. All labels and compressed incidences are derived; no connectivity or classification is an input. This incidence result still requires an actual cube nonembedding proof, and does not close the twenty-point obstruction or the external problem."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointCompression"))
        ]));
}
