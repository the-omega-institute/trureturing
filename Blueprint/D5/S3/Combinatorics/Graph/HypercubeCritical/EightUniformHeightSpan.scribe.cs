using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class EightUniformHeightSpanDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Private actual-edge height geometry consumed by eight-uniform Gray reconstruction.",
        H("The span of the centered signed height"),
        Blocks(
            Paragraph(Text(
                "For an actual balanced induced cubic support C of cardinality 54 in Q9, choose "
                    + "the given uniform bits a_i in the eight directions other than j. Uniformity "
                    + "always refers to the original globally even endpoint. Let W count the "
                    + "mismatches with a in those eight directions, and let h=W minus the indicator "
                    + "of original global odd parity. An occupied non-j edge preserves h. An "
                    + "occupied j-edge has even endpoint one level above its odd endpoint.")),
            Paragraph(Text(
                "If the maximum and minimum heights differ by at least two, their actual bands "
                    + "A and B are disjoint proper subsets of C. Each internal degree is two or "
                    + "three. At the minimum band all even vertices retain degree three; at the "
                    + "maximum band all odd vertices retain degree three. Their inherited graphs "
                    + "are bipartite and have girth at least eight. A nonempty neighbor-closed "
                    + "subset of C inherits balance and cubic regularity, so the existing actual "
                    + "54 lower bound makes it all of C. Thus each proper extreme band has a "
                    + "positive j-edge boundary.")),
            Paragraph(Text(
                "Represent each crossing edge by its coordinate-FALSE endpoint. The two actual "
                    + "boundary images are injective and disjoint subsets of the nine occupied "
                    + "j-edges, including when the height span is exactly two. With L the full-degree "
                    + "parity side and R the other side, actual handshake gives 3 card(L)+q=3 card(R). "
                    + "Both positive boundary counts are therefore three or six. For q=6, "
                    + "SixBoundarySideGap.six_boundary_side_gap and minimum degree two exclude "
                    + "orders two and four, leaving at least 28. For q=3, the existing actual "
                    + "side-path count gives e squared minus 14e plus 12 nonnegative, where e=card(L) "
                    + "and card(R)=e+1. Since e is at least two, the factorization "
                    + "(e-1)(e-13) excludes e at most thirteen. That band has at least 29 vertices. "
                    + "In particular both ends have at least 28, contradicting the total 54. "
                    + "The centered height consequently has span at most one."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeFiftyFourLowerBound")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/SixBoundarySideGap")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/SixBoundarySideCounting"))
        ]));
}
