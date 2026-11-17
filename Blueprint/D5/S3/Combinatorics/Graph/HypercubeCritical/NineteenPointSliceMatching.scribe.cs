using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class NineteenPointSliceMatchingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Private cubical matching-middle obstruction consumed by the nineteen-point slice theorem.",
        H("Three matching middles force the selected center"),
        Blocks(
            Paragraph(Text(
                "All declarations are private helpers consumed by NineteenPointSlice. "
                    + "The forced leaf incidences select fifteen actual slice points: six "
                    + "branch points and nine middles with the exact induced once-subdivision "
                    + "of K3,3 neighbor table. Three actual two-edge cube paths connect a "
                    + "selected center to the three opposite matching middles.")),
            Paragraph(Text(
                "Existing CubicalSubdivisionRigidity.normal_labels supplies an origin O "
                    + "and six distinct directions d(false,i), d(true,i), indexed by Fin 3. "
                    + "The matching middle i is O with its two corresponding directions "
                    + "flipped. The private three_matching_centers lemma takes only this "
                    + "injective direction map and distance at most two from a point p to "
                    + "each matching middle. It assumes no degree condition on any bridge.")),
            Paragraph(Text(
                "Let D be the coordinates where p differs from O and let P_i be the three "
                    + "disjoint direction pairs. The difference-set identity and each "
                    + "distance bound give card(D) at most twice card(D intersect P_i). "
                    + "Disjointness makes the sum of these intersections at most card(D), "
                    + "so three times card(D) is at most twice card(D). Thus p equals O. "
                    + "All six distinct selected branch points are then actual slice "
                    + "neighbors of p, contradicting its degree at most three. "
                    + "No bridge identification or exact-distance hypothesis is used."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/NineteenPointSliceIncidence")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/CubicalSubdivisionRigidity")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/CubeFiveNeighborGap"))
        ]));
}
