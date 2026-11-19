using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class TwentyPointPentagonCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual matching-coordinate rigidity", H("Actual matching-coordinate rigidity"),
        Blocks(
            Paragraph(Text("The actual perfect matching and complementary five-cycle labeling supply genuine coordinate flips. If all matching directions coincide, simultaneous flipping preserves each pairwise Hamming distance. Both compressed cycles then force the five high vertices on the first side to have pairwise distance two.")),
            Paragraph(Text("The common-center theorem and the original Huang negative ten-cycle argument exclude this constant-direction case using actual degree-two middles. Thus every surviving paired-pentagon realization has five distinct actual matching directions. The distinct-direction obstruction uses the resulting normalization and actual low independence."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointPentagonSigns"))
        ]));
}
