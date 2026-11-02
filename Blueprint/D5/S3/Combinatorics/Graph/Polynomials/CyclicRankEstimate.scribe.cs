using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Polynomials;

internal sealed class CyclicRankEstimateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Polynomials/CyclicRankEstimate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed rank-state polynomial has an exact finite coefficient decomposition. Its forest contribution is not generally the negative-binomial coefficient: on the triangle its cubic coefficient is zero, while the comparison coefficient is minus one. Actual graph rank bounds give nonnegative exponents, small support, a fixed-rank cyclic-state count through finite ordered-embedding codes, and rank-dependent term growth. The companion TutteCoefficientAsymptotics module consumes these bounds to control both forest error and cyclic contribution. The weaving geometry and Jones identification remain separate obligations.",
        H("Graph rank states and cyclic embedding counts"),
        Blocks(
            Node("state-exponent", "stateExponent", "State exponent", "The finite polynomial uses the Nat conversion of the integer exponent only after an explicit nonnegativity proof has been supplied.", DescribeRole.Definition),
            Node("state-exponent-integer", "stateExponentInteger", "Integer rank-state exponent", "The exponent is first formed in Z as v − 1 + s − 2q, before any conversion to a polynomial Nat exponent.", DescribeRole.Definition),
            Node("state-exponent-cast", "stateExponent_cast_eq_integer", "No-truncation exponent bridge", "Under the explicit integer nonnegativity hypothesis, the Nat exponent used by the polynomial casts back to the original integer rank-state exponent.", DescribeRole.Theorem),
            Node("state-term", "stateTerm", "Signed rank-state term", "Each subset state contributes its sign, rank power and (1+z) exponent to the integer polynomial.", DescribeRole.Definition),
            Node("state-polynomial", "statePolynomial", "Signed rank-state polynomial", "The polynomial is the finite sum over all edge-indexed subset states.", DescribeRole.Definition),
            Node("forest-states", "forestStates", "Forest states", "States with q(S)=|S| are selected as the forest part of the finite subset sum.", DescribeRole.Definition),
            Node("cyclic-states", "cyclicStates", "Cyclic states", "States with q(S)<|S| are selected as the cyclic part.", DescribeRole.Definition),
            Node("term-coefficient", "termCoefficient", "Coefficient of one state", "The coefficient of z^k in one state term is the signed binomial contribution when q(S)≤k and is zero otherwise.", DescribeRole.Definition),
            Node("ideal-coefficient", "idealCoefficient", "Ideal forest coefficient", "The comparison coefficient is Ring.choose (−b) k over the integers.", DescribeRole.Definition),
            Node("ideal-coefficient-formula", "idealCoefficient_formula", "Negative-binomial coefficient formula", "The ideal coefficient equals (−1)^k choose(b+k−1,k), including the b=k=0 boundary case.", DescribeRole.Theorem),
            Node("coeff-state-term", "coeff_stateTerm", "Exact state coefficient", "Polynomial coefficient extraction agrees with termCoefficient for every finite subset state.", DescribeRole.Theorem),
            Node("coeff-state-polynomial", "coeff_statePolynomial", "Exact finite coefficient sum", "The coefficient of the full state polynomial is the finite sum of the state coefficients.", DescribeRole.Theorem),
            Node("forest-coefficient", "forestCoefficient", "Forest coefficient", "The forest contribution is the sum of termCoefficient over forestStates.", DescribeRole.Definition),
            Node("cyclic-coefficient", "cyclicCoefficient", "Cyclic coefficient", "The cyclic contribution is the sum of termCoefficient over cyclicStates.", DescribeRole.Definition),
            Node("coeff-split", "coeff_split", "Forest/cyclic coefficient split", "Under the rank upper bound, every state belongs to exactly one of the forest and cyclic filters, so the full coefficient splits into the two contributions.", DescribeRole.Theorem),
            Node("graph-edge-predicate", "graphEdgePredicate", "Actual simple-graph edge predicate", "The graph wrapper lifts SimpleGraph adjacency to the unordered edge type Sym2(Fin n).", DescribeRole.Definition),
            Node("graph-edge", "graphEdge", "Actual graph edge type", "The graph wrapper restricts the finite edge index type to the actual adjacency predicate, so nonedges are not duplicated in the subset state sum.", DescribeRole.Definition),
            Node("graph-rank", "graphRank", "Actual graph rank state", "The graph wrapper computes rank from the connected-component count of the image of the actual edge subset, including isolated vertices.", DescribeRole.Definition),
            Node("graph-state-polynomial", "graphStatePolynomial", "Actual graph state polynomial", "For any positive vertex count, the polynomial sums over actual graph edge subsets. Exponent nonnegativity is proved from the component rank, rather than supplied as an extra premise.", DescribeRole.Definition),
            Node("state-graph", "graphOfState", "Spanning graph of a state", "The graph consists of the selected actual edges and retains every isolated vertex.", DescribeRole.Definition),
            Node("support-card", "support_card_le_twice_rank", "Support bound from graph rank", "A finite graph has at most twice its graph rank in nonisolated vertices. The proof uses a spanning forest with the same reachability relation and the degree-sum formula.", DescribeRole.Theorem),
            Node("graph-rank-bounds", "graph_rank_bounds", "Actual rank inequalities", "For a graph with a positive number of vertices, every state has rank at most its edge count and at most v minus one; the integer state exponent is nonnegative.", DescribeRole.Theorem),
            Node("graph-state-support", "graph_state_support_bound", "State support bound", "The actual rank-j state graph has at most 2j nonisolated vertices.", DescribeRole.Theorem),
            Node("ordered-sources", "orderedSources", "Sources of an ordered pattern", "A source has no adjacent vertex earlier in the specified finite vertex order.", DescribeRole.Definition),
            Node("forward-neighbors", "forwardNeighbors", "Forward neighbor carrier", "This carrier contains the actual later adjacent vertices of a vertex.", DescribeRole.Definition),
            Node("forward-degree", "boundedForwardDegree", "Bounded forward degree", "The supplied ordering has at most D later neighbors at every vertex. This is a graph property, not an assumed subset-count estimate.", DescribeRole.Definition),
            Node("ordered-embeddings", "orderedEmbeddings", "Increasing graph embeddings", "Increasing vertex maps preserve all edges of the support pattern.", DescribeRole.Definition),
            Node("cyclic-embedding-count", "cyclic_ordered_embedding_count", "Cyclic ordered embedding bound", "A cyclic simple pattern without isolated vertices has at most rank minus one source choices. A finite injection records source images and one bounded forward-neighbor slot for each remaining vertex, yielding the stated uniform embedding bound.", DescribeRole.Theorem),
            Node("cyclic-patterns", "cyclicPatterns", "Finite cyclic support patterns", "The finite carrier contains all simple patterns of the specified graph rank, with no isolated vertices and with an actual cycle.", DescribeRole.Definition),
            Node("cyclic-rank-states", "cyclicRankStates", "Cyclic states of one rank", "Only subsets with graph rank exactly j and more than j edges belong to this filter.", DescribeRole.Definition),
            Node("cyclic-rank-positive", "cyclic_graph_rank_ge_two", "Cyclic graph rank is at least two", "An actual cyclic edge subset of a simple graph has rank at least two; this excludes rank zero and makes the first coefficient exact.", DescribeRole.Theorem),
            Node("cyclic-pattern-constant", "cyclicPatternConstant", "Uniform pattern constant", "The constant depends only on D and j through finite carriers of simple support graphs on at most 2j vertices.", DescribeRole.Definition),
            Node("cyclic-rank-count-vertices", "cyclic_rank_state_count_vertices", "Rank-specific subset count", "Actual rank-j cyclic edge subsets inject into finitely many increasing support-pattern embeddings. The exponent of the vertex-count factor is j minus one.", DescribeRole.Theorem),
            Node("cyclic-rank-count", "cyclic_rank_state_count", "Uniform connected-graph cyclic count", "Connectedness replaces the vertex factor by an edge-count factor. The bound is uniform over all carrier sizes and graphs with forward degree at most D.", DescribeRole.Theorem),
            Node("graph-term-growth", "graph_term_coefficient_bound", "Rank-dependent state term growth", "A rank-j state contributes at most 2 to the k times (e plus one) to the k minus j in absolute value. The exponent and binomial bound are derived from actual graph ranks and edge counts.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create("cyclic-rank-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
