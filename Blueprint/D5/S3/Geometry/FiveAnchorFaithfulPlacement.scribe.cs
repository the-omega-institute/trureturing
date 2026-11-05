using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FiveAnchorFaithfulPlacementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A faithful placement of an entire finite bipartite graph with a side of size at most five and at most twenty-one edges.",
        H("Five anchors at the twenty-one-edge budget"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("five-anchor-placement"),
                DeclarationHandle.Create("D5/S3/Geometry/FiveAnchorFaithfulPlacement.exists_faithful_five_anchor_placement"),
                H("One injective placement on the original vertex type"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let V be any finite type, let G be a simple graph on V with decidable adjacency, "
                        + "and let A and B be finite subsets of V. Assume G.IsBipartiteWith A B and that "
                        + "every vertex belongs to A or B. Suppose that A has at most five vertices and "
                        + "G.edgeFinset has at most twenty-one edges. There is one map P from all of V "
                        + "to real Euclidean space indexed by Fin 5. It is injective, and for all ordered "
                        + "u,v in V, G.Adj u v if and only if dist(P(u),P(v)) equals one. Every A point "
                        + "has norm one quarter, every pair of A points has distance strictly below one, "
                        + "every B point has norm strictly between one quarter and one, and every pair "
                        + "of B points has distance strictly below two. Empty and singleton carriers, "
                        + "all isolates, diagonal pairs and same-side nonedges are included.")),
                    Paragraph(Text(
                        "Write r=1/4 and Omega={p:r<norm(p)<1}. With no anchors, enumerate the B "
                        + "vertices and put their scalar coordinates between one half and three quarters "
                        + "on a fixed coordinate axis. This gives distinct points with all distances "
                        + "below one. With at most four anchors, use affinely independent points on the "
                        + "radius-r sphere in four-dimensional space, embedded isometrically into the "
                        + "first four Fin 5 coordinates by extension by zero. A common-unit point in "
                        + "Omega is q=(sqrt(15)/4)e5.")),
                    Paragraph(Text(
                        "If there are five anchors and at most two full-neighborhood B vertices, "
                        + "use five affinely independent anchors in the same four-dimensional carrier. "
                        + "Their full common-unit locus is exactly {q,-q}. Place the full rows first, "
                        + "injectively at these poles. Both norms are in Omega, and their mutual "
                        + "distance is 2sqrt(15)/4, which is not one. Each remaining nonempty row has "
                        + "at most four anchors, so its orthogonal carrier has dimension at least two. "
                        + "Affine independence separates every nonneighbor anchor from that row's hull.")),
                    Paragraph(Text(
                        "If t is at least three full rows, the bipartite degree-sum identity counts "
                        + "five edges per full row. The sum of all other row sizes is therefore at "
                        + "most twenty-one minus five t, hence at most six. If every nonfull row has "
                        + "size at most three, choose five sphere points in three-dimensional space "
                        + "with every subset of at most four affinely independent, and embed them in "
                        + "Fin 5 by extension by zero. If a nonfull row H has size four, it is unique: "
                        + "every other nonfull row has size at most two by the residual bound. Put "
                        + "the four H anchors on an equatorial circle in sphere general position and "
                        + "the remaining anchor at the pole in the next coordinate. Every triple "
                        + "of anchors is independent; the pole lies outside the equatorial hull. "
                        + "These facts provide all nonneighbor separations needed for the small rows "
                        + "and for H. Every nonfull neighborhood has affine dimension at most two, "
                        + "and the full anchor family has affine span of dimension three. All directions "
                        + "lie in a carrier of dimension three, "
                        + "so even arbitrarily repeated full rows have positive-dimensional loci.")),
                    Paragraph(Text(
                        "Every nonempty row has the actual common-unit sphere supplied by "
                        + "CosphericalUnitLocus, and its Omega patch contains q. A previous B center "
                        + "has norm greater than r, so the existing common-unit avoidance theorem "
                        + "proves that its unit sphere cuts a proper section. A nonneighbor anchor "
                        + "is separated by its affine hull. Finite avoidance excludes all these "
                        + "unit distances and all previous B points. Empty rows use the radius-three-quarters "
                        + "sphere inside Omega, excluding every anchor and previous B unit sphere "
                        + "and every previous B point. Finite induction retains every old value and "
                        + "all previous invariants. Norm separation prevents A/B collisions. The "
                        + "two pole endpoints are checked explicitly; generic avoidance is applied "
                        + "only with an orthogonal carrier of dimension at least two.")),
                    Paragraph(Text(
                        "This theorem is the small-side component of a larger faithful-realization "
                        + "argument. It does not assert that every graph with at most twenty-one "
                        + "edges is covered by its small-side hypothesis, nor does it establish a "
                        + "graph-dimension extremal equality or a literature priority claim. Sphere "
                        + "sections, affine general position and orthogonal decomposition are classical "
                        + "tools; their existing repository suppliers are reused directly."))),
                DescribeRole.Theorem))));
}
