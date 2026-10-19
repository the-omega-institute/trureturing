using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.DirectSquareWeakFour;

internal sealed class DirectSquareWeakFourBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Bound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The universal linear lower estimate", H("The universal linear lower estimate"),
        Blocks(
            Paragraph(Text("The no-low-path restriction supplies the local hypothesis of the boundary-counting estimate. Row and column degree sums are reused from the metric-independent Hamming incidence core.")),
            Node("incidence-edges", "Edges equal landmarks", "incidence_edges",
                "For every landmark set, the edge cardinality of its bipartite incidence graph equals its landmark cardinality, as follows by summing the original row and column degrees and applying the degree-sum formula.", DescribeRole.Theorem),
            Node("no-low-walk", "Tagged low-path obstruction", "no_low_walk",
                "For n at least four, no three consecutive incidence edges can have all four vertex degrees two when the first and third vertices differ and the second and fourth differ. Bipartite tags reduce the statement to the rectangle-path obstruction.", DescribeRole.Theorem),
            Node("low-middle", "No adjacent low centers", "low_middle",
                "In the degree-two induced incidence graph of a weak-four set, a vertex with two low neighbors cannot be adjacent to another vertex with two low neighbors. Otherwise choosing a second neighbor at each endpoint gives the forbidden low path.", DescribeRole.Theorem),
            Node("linear-lower", "Universal minimum-degree-two estimate", "linear_lower",
                "For every n at least four and every weak-four landmark set with all row and column degrees at least two, 24n is at most eleven times the landmark cardinality. This is the twelve-elevenths graph estimate applied to the 2n incidence vertices.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role, resolution);
}
