using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.DirectSquareWeakFour;

internal sealed class DirectSquareWeakFourCoreDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Core.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shortest distances and weak-four separation in direct squares", H("Shortest distances and weak-four separation in direct squares"),
        Blocks(
            Paragraph(Text("Vertices are ordered pairs of labels. Adjacency requires both coordinates to differ. The metric is the minimum length of an actual walk in this graph. The source is Farhan, Kuziak and Yero, arXiv:2605.22307v1, Proposition 2.2. The introductory definition omits the word distinct; its intended restriction is explicit in Proposition 2.2. Including a self-pair would give separation zero for every landmark set.")),
            Node("graph", "Direct-product adjacency", "graph",
                "For every natural n, graph n is the finite simple graph on Fin n times Fin n in which vertices are adjacent exactly when both coordinates differ.", DescribeRole.Definition),
            Node("coord-dist", "Coordinate distance expression", "coordDist",
                "For any two coordinate types with decidable equality, coordDist is zero at equal pairs, one when both coordinates differ, and two otherwise.", DescribeRole.Definition),
            Node("distance-formula", "Actual shortest distances", "distance_formula",
                "For n at least three, the actual shortest-walk distance equals coordDist for every pair of vertices. A nonadjacent distinct pair has a common neighbor by choosing a third row and a third column. No assumed metric is used.", DescribeRole.Theorem),
            Node("connected", "Connectedness", "connected",
                "For every n at least three the actual direct-product graph is connected. Thus its natural graph distance never takes the disconnected junk value.", DescribeRole.Theorem),
            Node("delta", "Landmark separation", "delta",
                "For every finite landmark set S and pair x,y, delta S x y is the sum over w in S of Nat.dist between the actual graph distances from x and y to w.", DescribeRole.Definition),
            Node("is-weak-four", "All distinct pairs", "IsWeakFour",
                "A landmark set is weak four-resolving exactly when delta is at least four for every distinct pair of actual graph vertices.", DescribeRole.Definition),
            Node("wdim", "Least feasible cardinality", "wdim",
                "For every natural n, wdim n is the natural infimum of the achievable finite weak-four landmark cardinalities. At n at least four, the universal construction supplies a feasible set and the exact theorem proves that the infimum is an attained least cardinality.", DescribeRole.Definition),
            Node("delta-same-row", "Shared-row identity", "delta_same_row",
                "For n at least three, a row i and distinct columns j,jprime, separation equals the sum of their two column landmark degrees plus the membership indicators of the two compared vertices.", DescribeRole.Theorem),
            Node("delta-same-col", "Shared-column identity", "delta_same_col",
                "For n at least three, a column j and distinct rows i,iprime, separation equals the sum of their two row landmark degrees plus the membership indicators of the compared vertices.", DescribeRole.Theorem),
            Node("delta-rectangle", "Rectangle identity", "delta_rectangle",
                "For distinct rows i,iprime and distinct columns j,jprime, add the membership indicators of the compared diagonal vertices and twice those of the crossed corners to their separation. The result is the sum of the four row and column degrees. This identity follows by summing the contribution of each landmark.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role, resolution);
}
