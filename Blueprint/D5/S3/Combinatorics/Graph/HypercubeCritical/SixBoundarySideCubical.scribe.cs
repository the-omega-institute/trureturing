using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class SixBoundarySideCubicalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Private helpers consumed by the actual six-boundary side-gap theorem.",
        H("The actual fifteen-point cubical obstruction"),
        Blocks(Paragraph(Text("All helpers are private and consumed by the public side-gap theorem. Six core hexagon edges become branch points, the six core vertices become ring middles, and three actual antipodal degree-two middles complete an induced fifteen-point K3,3 subdivision. The omitted core vertex has three actual two-edge paths, through the off-cycle left labels, to the three matching ring middles. The existing NineteenPointSlice.labelled_matching_obstruction applies the actual cubical normal labels and three_matching_centers. Only the bridge path adjacencies are required; bridge degree two is never assumed. The forced origin has six selected branch neighbors and violates the original right degree bound three."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SixBoundarySideIncidence")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/NineteenPointSliceMatching"))
        ]));
}
