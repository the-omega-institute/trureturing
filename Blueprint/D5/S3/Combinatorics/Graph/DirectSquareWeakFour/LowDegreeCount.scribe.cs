using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.DirectSquareWeakFour;

internal sealed class DirectSquareWeakFourLowDegreeCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DirectSquareWeakFour/LowDegreeCount.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Boundary charging for degree-two vertices", H("Boundary charging for degree-two vertices"),
        Blocks(
            Paragraph(Text("All graphs in these statements are finite simple graphs. The low set need not be connected and may be empty. The estimates count actual neighbor incidences.")),
            Node("neighbors-in", "Neighbors in a set", "neighborsIn",
                "neighborsIn G A v is the subset of A adjacent to v.", DescribeRole.Definition),
            Node("sum-neighbors-in", "Two orders of incidence counting", "sum_neighborsIn",
                "For arbitrary finite vertex sets A,B and natural vertex weights f, the sum over v in A and neighbors w in B of f w equals the sum over w in B of f w times the number of its neighbors in A.", DescribeRole.Theorem),
            Node("low-boundary-bound", "Low vertices and outgoing edges", "low_boundary_bound",
                "Let L consist of degree-two vertices. Suppose that whenever two vertices of L are adjacent and the first has two neighbors in L, the second has at most one. Then twice the number of vertices in L is at most three times the number of edges from L to its complement. A local charge is summed; its internal transfers cancel by symmetry.", DescribeRole.Theorem),
            Node("boundary-le-degree", "Boundary capacity", "boundary_le_degree",
                "For every finite vertex set L, its outgoing-edge count is bounded by the total degree of vertices in its complement.", DescribeRole.Theorem),
            Node("excess-bound", "Twelve-elevenths edge bound", "excess_bound",
                "A finite simple graph of minimum degree at least two satisfying the stated local condition on its degree-two vertices has at least twelve elevenths as many edges as vertices. Split vertices into low and high sets. The low-boundary estimate and minimum high degree three combine with the degree-sum identity.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role, resolution);
}
