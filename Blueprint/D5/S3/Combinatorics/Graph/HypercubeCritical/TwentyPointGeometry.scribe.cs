using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class TwentyPointGeometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Twenty Point Geometry", H("Twenty Point Geometry"),
        Blocks(
            Paragraph(Text("This private unit excludes the 11/9 parity branch of the actual twenty-point slice in every cube dimension. The hypotheses are the actual induced support, original Huang balance, degrees two or three, independent lows, three and seven high vertices on the respective sides, and two low vertices on the nine-point side. Girth is derived from balance.")),
            Paragraph(Text("TwentyPointTheta supplies the derived actual theta incidence. Coordinate differences are taken from its actual central root. Three-step saturation gives the required Hamming distances; actual adjacency extends each two-coordinate root by one coordinate. Equal extra root coordinates force the two central vertices to have the same three-coordinate difference. Unequal extra root coordinates force actual degree-two middles to be the two-coordinate intersections, since the alternative four-coordinate union has an extra actual neighbor; one intersection is then adjacent to an actual low point, contradicting low independence.")),
            Paragraph(Text("The proof follows the local twenty-point obstruction argument for Hong–Wu–Xia Section 7 Problem 2 and reuses the private difference identities from CubeNineSupport at arbitrary dimension. It proves a branch exclusion, not the complete twenty-point obstruction or the external problem."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointTheta")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/CubeNineSupport"))
        ]));
}
