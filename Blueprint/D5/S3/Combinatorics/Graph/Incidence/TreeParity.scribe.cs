using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Incidence;

internal sealed class TreeParityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/Incidence/TreeParity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Even indegrees and prescribed odd-degree vertices in finite trees.",
        H("Tree cuts, indegrees and local degree parity"),
        Blocks(
            Paragraph(Text(
                "A head function chooses one endpoint of each undirected edge. The indegree of a vertex counts edges choosing it. In a tree, the branches at a vertex are in bijection with its neighbors. Removing the edge to a neighbor identifies the side of the cut containing that neighbor with its branch after deleting the vertex.")),
            Node("tree-parity-cut-rule", "even_indegrees_iff_odd_neighbor_branches",
                "Which branches send an edge inward",
                "For a finite tree of odd order and a head function choosing endpoints, all indegrees are even exactly when each neighbor edge points toward the designated vertex precisely when that neighbor's branch has odd order. Sum the indegrees on the branch side of the edge cut. Its internal tree edges number one less than its vertices, and only the cut edge can add a contribution."),
            Node("tree-parity-unique-orientation", "existsUnique_even_indegree_head",
                "The even-indegree orientation",
                "Every finite tree of odd order has a unique head function choosing endpoints and giving every vertex even indegree. The cut rule forces each head. The odd branches are even in number at every vertex, since their sizes sum to one less than the order of the tree."),
            Node("tree-parity-prescribed-degree-set", "exists_isTree_odd_neighborSet_card",
                "Realizing prescribed odd-degree vertices",
                "On a finite vertex type, every nonempty even finite subset is the odd-degree set of a tree. Put two marked vertices at the ends of a path, all unmarked vertices in its interior, and the remaining marked vertices as leaves attached to one endpoint. Relabel this tree on the given type."))));

    private static DocumentBlock Node(string id, string declaration, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);
}
