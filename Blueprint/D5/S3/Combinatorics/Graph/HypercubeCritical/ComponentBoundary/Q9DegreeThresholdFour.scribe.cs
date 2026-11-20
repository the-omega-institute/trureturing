using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9DegreeThresholdFourDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9DegreeThresholdFour.";

    public DocumentDefinition Create()
    {
        var cube = F.Seq(F.Id("Q"), F.Underscore, F.D(9));
        var vertexSet = F.Seq(F.Id("U"), F.Sp, F.Subseteq, F.Sp,
            F.Id("V"), F.Open, cube, F.Close);
        var cardinality = F.Seq(F.Bar, F.Id("U"), F.Bar, F.Eq, F.D(2, 6, 0));
        var degree = F.Seq(F.Delta, F.Open, cube, F.OpenBracket, F.Id("U"),
            F.CloseBracket, F.Close);

        return DocumentDefinition.Create(ScribeNode.Create(
            "The minimum induced maximum degree on 260 vertices of the nine-cube is four.",
            H("Optimal induced maximum degree at 260 vertices"),
            Blocks(
                Paragraph(Text(
                    "Write Q₉[U] for the graph induced by a vertex set U in the nine-cube "
                        + "and Δ for maximum degree. In the notation of Hong–Wu–Xia, "
                        + "fₖ(Q₉) minimizes Δ over induced subgraphs on 256 + k vertices. "
                        + "The two statements give f₄(Q₉) = 4.")),
                Describe.Lean(
                    DescribeId.Create("q9-260-maximum-degree-lower-bound"),
                    DeclarationHandle.Create(Prefix + "four_le_maxDegree_of_card_260"),
                    H("Every 260-vertex induced subgraph has maximum degree at least four"),
                    StatementSource.FromAuthor(F.Disp(F.Seq(F.Forall, F.Sp, vertexSet, F.Comma,
                        F.Sp, cardinality, F.Sp, F.Longrightarrow, F.Sp, F.D(4), F.Sp, F.Le,
                        F.Sp, degree))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Suppose Q₉[U] is subcubic and |U| = 260. The small-order "
                                + "classification gives size 54 or at least 72 for every "
                                + "Huang-balanced cubic component. The Gray54 extension "
                                + "obstruction bounds |U| by 257 if such a component has "
                                + "54 vertices. Thus each Huang-balanced cubic component "
                                + "has at least 72 vertices.")),
                        Paragraph(Text(
                            "The positive Huang eigenspace has dimension 256. Restricting "
                                + "to the 252 vertices outside U leaves a kernel of dimension "
                                + "at least four by rank-nullity. A supported eigenvector "
                                + "that is nonzero on a component saturates degree three "
                                + "there and gives Huang balance. Evaluation at one vertex "
                                + "of each balanced cubic component is injective on the "
                                + "supported eigenspace, so there are at least four such "
                                + "components. Their disjoint vertex sets would require "
                                + "at least 288 vertices."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("q9-260-maximum-degree-witness"),
                    DeclarationHandle.Create(Prefix + "exists_card_260_maxDegree_eq_four"),
                    H("A 260-vertex induced subgraph attains maximum degree four"),
                    StatementSource.FromAuthor(F.Disp(F.Seq(F.Exists, F.Sp, vertexSet, F.Comma,
                        F.Sp, cardinality, F.Sp, F.Land, F.Sp, degree, F.Eq, F.D(4)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Take both ninth-coordinate lifts of the 130-vertex set of "
                            + "Hong–Wu–Xia, Proposition 6.2. The explicit lifted set has "
                            + "260 vertices and maximum degree at most four. The lower "
                            + "bound gives equality "
                            + "(https://arxiv.org/html/2610.09483v1#S6.Thmtheorem2)."))),
                    DescribeRole.Theorem),
                Paragraph(Text(
                    "The original Hong–Wu–Xia question about f₂(Q₉) at 258 vertices "
                        + "remains open (arXiv:2610.09483v1, §7, Problem 2, "
                        + "https://arxiv.org/html/2610.09483v1#Thmproblem2)."))),
            []));
    }
}
