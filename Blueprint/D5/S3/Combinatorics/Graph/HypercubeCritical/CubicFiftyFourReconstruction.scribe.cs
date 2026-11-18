using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class CubicFiftyFourReconstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every actual induced cubic Huang-balanced 54-vertex Q9 support is a whole-cube image of Gray support.",
        H("Reconstruction of balanced cubic fifty-four vertex supports"),
        Blocks(
            Paragraph(Text(
                "Let C be a finite set of functions Fin 9 to Bool. Its graph is the actual "
                    + "induced cube graph: two selected vertices are adjacent exactly when "
                    + "they differ in one coordinate. Assume this graph is regular of degree "
                    + "three, C satisfies IsBalanced for the fixed FALSE-prefix Huang matrix, "
                    + "and C has 54 vertices. There exist a total equivalence g of the entire "
                    + "nine-dimensional Boolean cube and a permutation pi of all nine "
                    + "coordinates such that g(flip(x,i))=flip(g(x),pi(i)) for every cube "
                    + "vertex x and coordinate i, and C is the image of GrayGridComponent.support(3) "
                    + "under g. Nonemptiness, girth, short walks and the thin coordinate half "
                    + "are consequences of the three assumptions.")),
            Paragraph(Text(
                "BalancedCubeGirth supplies girth at least eight. HammingSeven supplies "
                    + "Hamming diameter at most seven and the actual radius-three Moore "
                    + "neighborhoods. The root, first, second and third layers have sizes "
                    + "1, 3, 6 and 12, so each ball has 22 vertices. Every third-layer vertex "
                    + "has one inner neighbor and two outward neighbors. These are actual "
                    + "selected vertices and edges, not an assumed abstract tree model. "
                    + "The direction-edge identity gives nine edges in each coordinate. "
                    + "After faithful coordinate transport, the slice degree-two/degree-three "
                    + "handshake makes every literal coordinate half odd.")),
            Paragraph(Text(
                "First suppose selected x and y differ in seven coordinates. Their "
                    + "radius-three balls A and B are disjoint, leaving ten vertices O. "
                    + "Write k for the number of edges between A and B. Each ball has "
                    + "24 outward incidences, and O can receive at most thirty incidences. "
                    + "Thus 48 is at most 2k+30 and k is at least nine. An edge leaving a "
                    + "ball starts in its third layer, where each vertex has capacity two; "
                    + "there are at least five cross-incident leaves in each ball. Their "
                    + "second-layer parents have capacity two, giving at least three parents.")),
            Paragraph(Text(
                "Let T be the two coordinates on which x and y agree. The Boolean "
                    + "difference-set identity d(x,y)+2|diff(x,z) intersect diff(y,z)| "
                    + "=d(x,z)+d(y,z) shows that the cross-incident leaves and their root "
                    + "paths agree on T. Every root neighbor agrees on T as well: otherwise "
                    + "its distance from the other root would exceed seven. Each ball "
                    + "therefore contributes at least 1+3+3+5=12 vertices to the common "
                    + "T-face F00, so its size n00 is at least 24. A vertex differing on "
                    + "both T-coordinates has distance sum at least eleven from the two "
                    + "roots; diameter seven excludes it from either ball. Hence the "
                    + "opposite face F11 has size n11 at most ten. The two opposite literal "
                    + "halves have size sum 54-n00+n11 at most forty. Both sizes are odd, "
                    + "so one is at most nineteen.")),
            Paragraph(Text(
                "If no selected pair has distance seven, the Hamming diameter is at "
                    + "most six. At any root, the twelve third-layer vertices have twenty-four "
                    + "outward incidences. Their union outside the ball has at least eight "
                    + "vertices by cubicity. Each has a walk of length four, even relative "
                    + "parity, and lies outside the ball; its Hamming distance is two or "
                    + "four. No assumption that every fourth-neighborhood vertex has "
                    + "Hamming distance four is used. If nk counts selected vertices at "
                    + "Hamming distance k from the root, then n2 is at least six, n3 is at "
                    + "least twelve, and n2+n4 is at least fourteen, since the second layer "
                    + "and this fourth neighborhood are disjoint.")),
            Paragraph(Text(
                "The global cubic bipartite handshake gives 27 vertices of each cube "
                    + "parity without assuming connectedness. With n0=1, n1=3 and diameter "
                    + "six, the integer distance sum D at any root satisfies "
                    + "D+2n2+2n3+2(n2+n4)=279. Thus D is at most 215. For a coordinate "
                    + "let a and b be the sizes of its FALSE and TRUE halves. Coordinate "
                    + "Fubini counting gives the ordered-pair distance sum as twice the "
                    + "sum of a*b over the nine coordinates. If every half had at least "
                    + "eighteen vertices, a+b=54 would imply a*b at least 18*36=648. "
                    + "The total would be at least 2*9*648=11664, contradicting its upper "
                    + "bound 54*215=11610. Therefore a literal half has size at most "
                    + "seventeen, and in particular at most nineteen.")),
            Paragraph(Text(
                "In either case choose the derived coordinate j and Boolean value b. "
                    + "The coordinate permutation p swapping j with zero induces R(x)(k) "
                    + "=x(p inverse(k)). This is an equivalence of the whole cube, "
                    + "intertwines all flips and transports actual induced regularity. "
                    + "HuangCubeCovariance supplies a source-coordinate sign gauge theta. "
                    + "For an original switching function sigma, the transported function "
                    + "at y is theta(R inverse(y))*sigma(R inverse(y)). Its real edge "
                    + "equation proves original Huang balance of C'=R(C); balance invariance "
                    + "is not assumed. The derived half becomes coordinate zero, where "
                    + "NineteenPointSlice applies with its unchanged actual-support "
                    + "telescope. If its equivalences are g' and pi', compose g as R inverse "
                    + "after g' and pi as p inverse after pi'. This proves every flip "
                    + "equation and the image equality for the original C.")),
            Paragraph(Text(
                "Moore neighborhood counting is a classical method; see Noga Alon, "
                    + "Shlomo Hoory and Nathan Linial, The Moore Bound for Irregular Graphs, "
                    + "Graphs and Combinatorics 18 (2002), 53-57, "
                    + "https://doi.org/10.1007/s003730200002. The result is a repository-derived "
                    + "structural reconstruction for the stated balanced cubic supports. "
                    + "The external anchor is Hong, Wu and Xia, Graph Sensitivity of "
                    + "Cartesian Products with Matched Bridges, arXiv:2610.09483v1, "
                    + "Section 7 Problem 2, https://arxiv.org/html/2610.09483v1#Thmproblem2 . "
                    + "The original f2(Q9) problem and the 258-vertex obstruction remain open.")),
            Describe.Lean(
                DescribeId.Create("actual-cubic-fifty-four-gray-reconstruction"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/HypercubeCritical/CubicFiftyFourReconstruction.gray_reconstruction"),
                H("Whole-cube Gray reconstruction from the original three assumptions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every C : Finset(Q9), actual induced degree-three regularity, "
                        + "original IsBalanced C and C.card=54 imply existence of "
                        + "g : Q9 equiv Q9 and pi : Fin 9 equiv Fin 9 such that, for all "
                        + "x : Q9 and i : Fin 9, g(flip(x,i))=flip(g(x),pi(i)), and "
                        + "C=(GrayGridComponent.support 3).image g. No supplied half-size, "
                        + "girth, uniformity, normal form or geometry premise occurs."))),
                DescribeRole.Theorem))));
}
