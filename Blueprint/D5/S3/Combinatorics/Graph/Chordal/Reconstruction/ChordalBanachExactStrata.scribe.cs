using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Chordal.Reconstruction;

internal sealed class ChordalBanachExactStrataDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/Chordal/Reconstruction/ChordalBanachExactStrata";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Circumference determines the scalar reconstruction coefficient of a finite chordal graph. Finite modular tests, elimination orderings, root paths, and finite Hilbert centers give reconstruction laws in other targets.",
        H("Exact chordal reconstruction strata"),
        Blocks(
            Result("scalar-circumference", "scalar_circumference_exact", "The scalar circumference formula",
                "Let G be finite and chordal, with a simple cycle of greatest length L. Orient each edge both ways with opposite real gains and suppose every triangle defect has absolute value at most one. There is a potential with every edge residual bounded by one minus two over L. A single gain assignment forces some edge residual at least that large for every potential.",
                "Triangulation bounds the signed sum on any simple cycle of length l by l minus two in absolute value. Adding one minus two over L to each directed gain makes simple cycles and backtracks nonnegative. Repeated-vertex decomposition extends this to closed walks. Infima of directed walk costs give the potential inequalities. Along a longest cycle, unit gains along the path and minus one on its closing edge give the matching lower bound by telescoping."),
            Result("finite-modulus", "finite_modulus_decides_abelian_reconstruction", "A finite test for universal abelian reconstruction",
                "Let G be finite, linearly ordered on vertices and chordal, and let T be a spanning tree contained in G. For a natural budget k and modulus q greater than three k plus one, a single cochain over the integers modulo q decides universal abelian feasibility. It assigns zero to tree edges and a separate signed coordinate to each edge outside the tree. Universal feasibility allows every additive abelian target and every set containing zero and the triangle defects. A potential uses sums of k elements of the allowed set as residuals.",
                "Lift the modular residuals to short integer sums, choosing opposite lifts on opposite orientations. Every coordinate of a triangle discrepancy is a multiple of q with absolute value at most three k plus one, so it vanishes. The lifted residuals integrate to a potential by chordality. In any abelian target, first gauge the tree to zero, then send each integer basis element to the normalized gain of its edge."),
            Result("ancestor-power", "exists_ancestor_banach_gain_potential", "Bounded ancestor edges of a rooted tree",
                "Root a tree at any vertex. Join two distinct vertices when one is on the root path of the other and their distance is at most the positive integer k. For skew gains in a real seminormed vector space with triangle defect at most epsilon, all edge residuals are bounded by epsilon times two minus two over k.",
                "For each depth residue modulo k, integrate on the chain of marked ancestors and then along each branch to the vertex. Across one edge, at most one marked depth is crossed. The norm bound counts at most one triangle per endpoint, with no charge when that endpoint is marked. Each endpoint is marked in one residue class, and the average potential gives the claimed bound."),
            Result("group-four", "exists_clique_four_group_gain_potential", "Group reconstruction at clique number four",
                "Let a finite chordal graph have every clique of size at most four. Gains are inverted upon reversal in a group whose pseudometric is invariant under left and right multiplication. If every triangle defect is at most epsilon, the edge errors of one potential are at most twice epsilon.",
                "In reverse simplicial elimination, record a two-factor residual on each edge and an ordering of each triangle with two controlled comparisons. The insertion rule supplies all three new triangle orderings and preserves the earlier ones."),
            Result("group-five", "exists_clique_five_group_gain_potential", "Group reconstruction at clique number five",
                "For finite chordal graphs with cliques of size at most five under the same group and gain assumptions, a potential gives edge errors at most three times epsilon.",
                "Order each four-clique so that its successive path prefixes have budgets one, two, and one. The insertion rule propagates those budgets to all child faces. Available copies of an earlier neighbor fill out the frame for smaller separators."),
            Result("walk-factors", "closed_walk_triangle_factors", "Closed walks factor through triangles",
                "For a closed walk p in a finite chordal graph and inverse-compatible gains in any group, there is a list F of length at most the length of p minus two, truncated at zero, whose ordered product is the gain of p. Each factor is a conjugate of the holonomy of an oriented triangle. Length subtraction is natural, so a trivial walk or a backtrack uses zero factors.",
                "Rotate to a simplicial vertex in the induced support. Either delete a backtrack or close a triangle across its two neighbors. Conjugate the shorter factorization back to the original basepoint."),
            Result("tree-spanner", "exists_tree_spanner_approximate_gain_potential", "Group reconstruction from a tree spanner",
                "Suppose a spanning tree T of a finite chordal graph is contained in the graph and every graph edge has endpoints at tree distance at most t. The group and defect hypotheses are those of the clique bounds.",
                "Integrate the gains on the tree. Closing a tree path with one graph edge gives a loop of length at most t plus one. Its triangle factors bound the residual by t minus one times the defect."),
            Result("radius", "exists_radius_approximate_gain_potential", "Group reconstruction from graph radius",
                "Let the finite connected chordal graph have a vertex at distance at most r from every vertex. The same group and gain hypotheses apply. A potential integrates chosen shortest root walks, and each graph edge closes a loop of length at most two r plus one. The edge residual is at most two r minus one times the defect."),
            Result("hilbert", "exists_hilbert_jung_gain_potential", "Hilbert reconstruction from finite Jung centers",
                "Let G be finite and chordal with cliques of size at most k plus one, for k at least one. The target is any real inner product space. For skew gains whose triangle defects have norm at most epsilon, one potential bounds all edge residuals by J divided by one minus J, times epsilon. Here J is the square root of the ratio of k minus one to twice k.",
                "At each simplicial insertion, the candidate labels are at pairwise distance at most the sum of the old error bound and epsilon. A finite Jung center for at most k candidates shrinks that diameter by J. The factor J divided by one minus J is the fixed point of this estimate."),
            Result("clique-tree-height", "cliqueTree_height_banach_gain_potential", "A finite-height clique-tree bound",
                "Let the adjacent bags of a clique tree meet in at least one and at most q vertices, where q is at least two. If the tree has a root at distance at most h from every bag, every skew Banach gain assignment of defect at most epsilon admits a potential with residual at most epsilon times q minus one minus the product of q minus two and the h-th power of the ratio of q minus one to q.",
                "Distances through the root bound the clique-tree diameter by twice h. The center-extension recurrence begins at one and applies the separator averaging update. Solving this recurrence gives q minus one minus the product of q minus two and the h-th power of the ratio of q minus one to q."),
            Result("group-path-strata", "pathPower_group_exact_strata", "Exact group bounds on finite path powers",
                "For positive width k, the least nonnegative bound over every finite path power and every bi-invariant group is zero, one, or two, according as k is one, two, or at least three.",
                "Consecutive-edge integration handles the first two widths. The existing interval potential supplies the upper bound two. At width two a nonflat triangle in an integral word metric forces unit error. At every larger width the cyclic group of order 49 gives a word-budget obstruction, pulled back from width three along a depth collapse."),
            Result("l1-jung", "exists_l1_jung_gain_potential", "Real L1 reconstruction from odd Jung centers",
                "Let G be finite and chordal with cliques of size at most two m plus two, for m at least one. For any measure and skew real L1 gains of triangle defect at most epsilon, one potential gives residual at most two m minus one times epsilon. Clique bounds four and six give factors one and three.",
                "The pointwise lattice median and the explicit nonnegative weights give a Jung center for up to two m plus one candidate gains. In simplicial elimination its radius factor is one minus one over two m. Solving the radius recurrence gives the stated coefficient."),
            Result("group-integrality", "group_coefficient_integral", "Integrality of the universal group coefficient",
                "The optimal universal coefficient of a finite connected chordal graph is an integer between zero and four. Normalize along a spanning tree. In the canonical free group on non-tree edges, the triangle holonomies and their conjugates generate all labels.",
                "The induced word metric has integral distances. Every target gain after tree normalization is the image of the canonical free-group cochain. Its triangle bounds carry each generator into the unit ball, so a shortest word-budget potential controls every target. The free-group example attains this budget."),
            Result("cyclic-width-three", "pathPower_width_three_cyclic_exact", "The cyclic reconstruction witness at width three",
                "For each width-three path power with at least fourteen vertices, a cyclic group of order 49 with the specified Cayley generators admits gains of defect at most one and exact optimal error two. These interval graphs are chordal and have no clique of size greater than four.",
                "The period-three gain pattern is zero on consecutive edges. A unit-error potential would have increments in the unit word ball. Exact checks on the last two increments eliminate every possible continuation by the fourteenth vertex. The two-factor clique potential gives the matching upper bound. Applying the existing Banach path-power estimate at width three gives four thirds, strictly below two."),
            Result("l1-clique-four-exact", "l1_clique_four_exact", "Exact real L1 coefficient at clique number four",
                "For every nonzero real L1 space, the optimal uniform coefficient on finite chordal graphs of clique number at most four is one. The zero space has coefficient zero.",
                "The three-candidate median gives the upper bound under simplicial elimination. Chordal fans have unbounded circumference at clique number three. Unit-vector scalar gains on these fans preserve the scalar lower bound by applying a norm-one functional to every potential."),
            Result("cyclic-subtwo-refutation", "not_subtwo_cyclic_path", "No sub-two fit for the cyclic cochain",
                "On the width-three power of the twenty-seven-vertex path, the specified cyclic gain in the Cayley metric of order 49 has some residual at least two for every potential. The metric has integer distances, so a sub-two fit would use at most one generator on every edge. The word certificate rules out such a fit."),
            Result("pair-retention", "family_exact", "Exact coefficient of the pair-retention family",
                "Start with a clique of size m at least three. At each of D generations, attach a clique of n fresh vertices together with each retained pair in each current bag. In every nonzero real normed space the least uniform residual over gains of triangle defect at most one is one minus two divided by the product of m and the D-th power of n plus one.",
                "The sharp extension along each pair multiplies the gap from one by the reciprocal of n plus one. Traversing all fresh vertices along each edge of a distinguished cycle multiplies its length by n plus one. Ordered gains in a unit direction give the matching obstruction."),
            Result("power-path-radius", "powerPath_uniform_ge_doubled_radius", "Power-path lower bound from a finite family",
                "Take k indexed points of diameter at most one in a real seminormed space. Suppose every ball containing their doubles has radius at least r. Any nonnegative coefficient C valid for every finite width-k path power is at least r.",
                "Assign the translated point of the starting residue as the gain of a short forward edge and twice that point on edges of length k. At defect at most one, a fit of size C on M plus one rows gives an enclosing ball of radius at most C plus twice C divided by M. Arbitrarily large M gives the result."),
            Result("hilbert-power-path-lower", "hilbert_powerPath_uniform_lower", "The Hilbert power-path lower bound",
                "For any positive width k, a nonnegative coefficient valid for all finite width-k path powers with gains in real k-dimensional Euclidean space is at least the square root of two minus two over k.",
                "The normalized regular simplex has diameter one. The squared distances of its doubled vertices from a common center average to two minus two over k plus the squared distance of that center from the simplex centroid. Apply the finite-family radius lower bound."),
            Result("even-width-l1-power-path", "l1_even_powerPath_exact", "Exact finite-dimensional L1 bound at even widths",
                "At width two m with m positive, the least uniform coefficient over all path lengths for the real L1 space on the permutations of two m labels is two minus two over two m.",
                "Every coordinate separates the labels into two halves. Symmetry makes the distances between distinct sample points equal. Any center has total distance at least the contribution from these balanced cuts. The periodic radius construction gives the lower bound, and the general Banach path-power theorem gives the upper bound."))));

    private static DocumentBlock.Describe Result(string id, string declaration, string heading,
        params string[] paragraphs) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(paragraphs.Select(p => Paragraph(Text(p))).ToArray()), DescribeRole.Theorem);
}
