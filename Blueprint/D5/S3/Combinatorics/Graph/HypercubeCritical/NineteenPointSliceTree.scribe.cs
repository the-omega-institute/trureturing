using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class NineteenPointSliceTreeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Private double-root counting and equality-tree construction for the nineteen-point slice obstruction.",
        H("The sharp nineteen-point double-root tree"),
        Blocks(
            Paragraph(Text(
                "All declarations are private helpers consumed by NineteenPointSlice. "
                    + "For a finite bipartite graph of girth at least eight, with degrees two or "
                    + "three and independent degree-two vertices, the existing EighteenPointSlice "
                    + "path and layer lemmas give disjoint depth-three trees about a high-high edge. "
                    + "Each high first neighbor adds one to the eighteen-point lower bound.")),
            Paragraph(Text(
                "At nineteen vertices with eleven low vertices, only eight vertices are high "
                    + "and at most two highs have a high neighbor. The two roots already occupy "
                    + "those positions. First neighbors must be low, and high leaves would create "
                    + "another high-high incidence. The roots, four middle positions and at most "
                    + "one outside vertex cannot contain all eight highs, a contradiction.")),
            Paragraph(Text(
                "With nine low and ten high vertices, incidence counting forces a high vertex "
                    + "with two high neighbors. The sharp tree bound is then an equality: all "
                    + "nineteen vertices are covered. The private forward-neighbor lemmas and "
                    + "existing girth path uniqueness construct an injective nineteen-label tree "
                    + "with the actual internal neighbor sets. The same sharp count bounds the "
                    + "sum of high-neighbor counts across every high-high edge by three. "
                    + "These are graph arguments used inside the actual slice proof, with no "
                    + "graph classification supplied as an assumption."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/EighteenPointSlice"))
        ]));
}
