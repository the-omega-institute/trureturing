using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.DirectSquareWeakFour;

internal sealed class DirectSquareWeakFourLowerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Lower.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Necessary incidence restrictions for weak-four landmarks", H("Necessary incidence restrictions for weak-four landmarks"),
        Blocks(
            Paragraph(Text("The incidence graph has separate row and column vertices and one edge for each landmark. It is distinct from the ambient direct-product graph.")),
            Node("row-pair-min", "Necessary row pair bound", "row_pair_min",
                "For n at least four, every two distinct rows of a weak-four set have total landmark degree at least four. If their total degree were at most three, a column outside both supports would give a pair separated by at most three.", DescribeRole.Theorem),
            Node("col-pair-min", "Necessary column pair bound", "col_pair_min",
                "For n at least four, every two distinct columns of a weak-four set have total landmark degree at least four, by the transposed support argument.", DescribeRole.Theorem),
            Node("minimum-degrees", "Minimum incidence degree", "minimum_degrees",
                "For n at least four, a weak-four landmark set with fewer than 3n minus 2 landmarks has every row and column degree at least two. A degree-zero row forces all other degrees at least four; a degree-one row forces all others at least three. The column argument is identical in its parameters.", DescribeRole.Theorem),
            Node("incidence", "Bipartite incidence graph", "incidence",
                "For a landmark set S, incidence S is the simple graph on the disjoint union of row and column labels, with edge between row i and column j exactly when the pair belongs to S.", DescribeRole.Definition),
            Node("incidence-degrees", "Exact incidence degrees", "incidence_degrees",
                "At every order, the incidence degree of a row label equals its row landmark cardinality, and the degree of a column label equals its column landmark cardinality.", DescribeRole.Theorem),
            Node("no-low-rectangle-path", "Forbidden low path", "no_low_rectangle_path",
                "A weak-four set at order at least four cannot contain the three edges of a four-vertex incidence path when all four endpoint degrees are two. The crossed product pair then has separation at most three.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role, resolution);
}
