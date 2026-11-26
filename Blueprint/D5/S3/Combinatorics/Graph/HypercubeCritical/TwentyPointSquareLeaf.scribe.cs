using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class TwentyPointSquareLeafDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Paired squares with leaves", H("Paired squares with leaves"),
        Blocks(
            Paragraph(Text("Each derived square-with-leaf compressed graph is transported by a graph isomorphism to the labels a0,a1,a2,a3 around the square and a4 at the leaf on a0. The opposite side has corresponding labels b0 through b4. Exact compressed neighbor tables, five high vertices on each side, and actual low-path incidence justify these isomorphisms.")),
            Paragraph(Text("Actual high-neighbor degrees are three minus the compressed degrees. The two high neighbors of a leaf must be separated by at least three compressed edges. In the opposite square with a leaf, the only such pair is its leaf and the opposite square vertex. Hence a4 meets b2 and b4, and b4 meets a2 and a4. The remaining high vertices a1 and a3 match b1 and b3; the graph automorphism exchanging b1 and b3 fixes the orientation. The exact actual high edges are a2-b4, a4-b4, a4-b2, a1-b1, and a3-b3.")),
            Paragraph(Text("This derives the high-edge table used by the local twenty-point obstruction argument for Hong–Wu–Xia Section 7 Problem 2. The positive eight-cycle coordinate-word classification and the resulting square-with-leaf geometric contradiction are separate mathematical steps."))),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointPentagonExclusion"))]));
}
