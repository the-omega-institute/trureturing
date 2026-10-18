using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.DirectSquareWeakFour;

internal sealed class DirectSquareWeakFourDesignDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DirectSquareWeakFour/Design.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A sufficient incidence criterion and its assembly laws", H("A sufficient incidence criterion and its assembly laws"),
        Blocks(
            Paragraph(Text("These criteria concern an incidence graph, not a disjoint union decomposition of the actual direct-product graph. Their separation consequence includes pairs with coordinates in different incidence blocks.")),
            Node("good", "Sparse incidence criterion", "Good",
                "A finite bipartite incidence set is Good when every row and column degree is at least two, every simple three-edge path has endpoint degree total at least nine, and no rectangle has all four corners selected.", DescribeRole.Definition),
            Node("good-resolves", "All-pair sufficiency", "good_resolves",
                "At order at least three, every Good incidence set is an actual weak-four landmark set. Shared-coordinate pairs use minimum degree two. A rectangle with at most two selected corners uses total degree at least eight; three corners use the path degree bound nine; four corners are excluded.", DescribeRole.Theorem),
            Node("good-join", "Disjoint incidence union", "good_join",
                "For arbitrary coordinate types with decidable equality, the disjoint incidence union of two Good sets is Good. Every three-edge path and every four-cycle lies entirely in one of the two blocks. Degrees are preserved by the original union counting lemmas.", DescribeRole.Theorem),
            Node("good-map", "Coordinate relabeling", "good_map",
                "For arbitrary equivalences of the two coordinate parts, mapping a Good incidence set along their product preserves all four conditions.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role, resolution);
}
