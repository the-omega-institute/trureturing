using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class TwentyPointCompressionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Twenty Point Compression", H("Twenty Point Compression"),
        Blocks(
            Paragraph(Text("Private proof organization for the actual twenty-point slice obstruction in the Hong–Wu–Xia Section 7 Problem 2 branch. Every compressed edge has an actual degree-two middle in the induced support. No compression or incidence is assumed as input.")),
            Paragraph(Text("Actual short-path uniqueness gives the compression degree identity and triangle exclusion. For a nine-point opposite parity class, three-step saturation forces each high neighbor to have exactly one high neighbor, and every nonneighbor has actual Hamming distance three. The two opposite low points form a path through the three high roots; its central high neighbor has two compressed neighbors with no actual high neighbor.")),
            Paragraph(Text("These helpers are consumed by TwentyPointSlice. They are intermediate consequences of actual degrees, independent lows and girth derived from original Huang balance, following the local twenty-point argument; they do not constitute the completed obstruction or close the external Problem 2."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/EighteenPointSlice")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricHighGraph")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/FifteenSliceStructure")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricLowPartners"))
        ]));
}
