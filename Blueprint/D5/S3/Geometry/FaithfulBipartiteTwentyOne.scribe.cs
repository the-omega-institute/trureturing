using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FaithfulBipartiteTwentyOneDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One faithful injective realization of the entire original carrier at the twenty-one-edge budget.",
        H("Faithful bipartite realizations in real five-space"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("faithful-twenty-one"),
                DeclarationHandle.Create("D5/S3/Geometry/FaithfulBipartiteTwentyOne.exists_faithful_realization_of_card_edges_le_twenty_one"),
                H("The full original-carrier theorem"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any finite type V and simple graph G on V with decidable adjacency, "
                        + "assume G.IsBipartite and G.edgeFinset.card is at most twenty-one. "
                        + "There exists one total map P from V to EuclideanSpace over the reals "
                        + "indexed by Fin 5. The map is injective, and for every ordered pair u,v "
                        + "of original vertices, G.Adj u v if and only if dist(P(u),P(v)) equals one. "
                        + "This includes an empty carrier, all isolated vertices, and every diagonal.")),
                    Paragraph(Text(
                        "Take the two color classes A and B of the actual Fin 2 coloring. "
                        + "Every original vertex has one of these two colors, including every isolate. "
                        + "Let C consist of A vertices of original degree at least three and let H "
                        + "consist of A vertices of original degree at least five. The pointwise "
                        + "degree bound gives 3|C|+2|H| at most the left degree sum, which is the "
                        + "number of edges. Thus either |C| is at most five or |H| is at most one.")),
                    Paragraph(Text(
                        "In the small-core case induce G on C union all of B. Its edge count is "
                        + "at most the original edge count, and its C side has at most five vertices. "
                        + "FiveAnchorFaithfulPlacement supplies an injective all-pair faithful map "
                        + "of this actual subtype with B diameter strictly below two. Keep every "
                        + "B vertex even if it becomes isolated in this induced graph. Every omitted "
                        + "original vertex belongs to A, has original degree at most two, and has "
                        + "its entire original neighborhood in B. LowDegreeFaithfulExtension restores "
                        + "all these vertices while fixing every old label coordinate.")),
                    Paragraph(Text(
                        "For the exceptional case select distinct radius-one-quarter points y on "
                        + "the three-sphere in the first four coordinates with every at most five "
                        + "affinely independent, using SphereGeneralPosition. If there is no high "
                        + "vertex use this configuration directly. If the unique high vertex is "
                        + "adjacent to all B vertices, use the same configuration and the explicitly "
                        + "verified point (sqrt(15)/4)e5. If its neighborhood K is proper, replace "
                        + "each B point by (sqrt(3)/2)y plus e5/8 on K and minus e5/8 outside K. "
                        + "These points still have norm one quarter. Equatorial projection recovers "
                        + "the same nonzero uniform multiple of y, retaining all required affine "
                        + "independences. Choose the explicit exceptional point "
                        + "p=((1+sqrt(61))/8)e5. Writing k=(1+sqrt(61))/8, "
                        + "its squared distance to a B point is k^2+1/16 minus twice k times "
                        + "that point's last coordinate. The identity k^2-k/4=15/16 gives unit "
                        + "distance exactly on K; outside K the squared distance is 1+k/2, "
                        + "strictly greater than one. No avoidance argument is applied to a "
                        + "two-point locus, and the exceptional degree is not bounded.")),
                    Paragraph(Text(
                        "Retain only the original A vertices of degree at least three. Every "
                        + "ordinary retained vertex has degree three or four, so its actual common-unit "
                        + "locus has orthogonal carrier dimension at least two. CosphericalUnitLocus "
                        + "constructs a nonempty sphere there. Affine general position separates "
                        + "every B nonneighbor from the neighborhood hull. Every previously placed "
                        + "positive-degree A point has norm at least three quarters, since it is at "
                        + "unit distance from a norm-one-quarter B point. Its unit sphere therefore "
                        + "cuts a proper section of the new locus. The existing finite-section "
                        + "avoidance theorem excludes all previous A unit distances and collisions. "
                        + "Norm separation prevents A/B collisions, and the B diameter is at most "
                        + "one half, hence strictly below one. Restore every omitted degree-zero, "
                        + "one, or two A vertex with the actual low-degree extension theorem. "
                        + "Its equality on old labels preserves this strict B diameter.")),
                    Paragraph(Text(
                        "The exceptional geometry is private consumed content in this module, "
                        + "on the live proof path of the public full theorem. The theorem neither "
                        + "assumes a geometric selection oracle nor discards unsupported original "
                        + "vertices. Alon and Kupavskii (2014) provide the known twenty-two-edge "
                        + "obstruction motivating this threshold. That obstruction is not formalized "
                        + "here; no formal extremal equality g2(5)=22 or worldwide novelty claim "
                        + "is made. The separate centered-distance-matrix and original-projective-plane "
                        + "contracts are not conclusions of this theorem."))),
                DescribeRole.Theorem))));
}
