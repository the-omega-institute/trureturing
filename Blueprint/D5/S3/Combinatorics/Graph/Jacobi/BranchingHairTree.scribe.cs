using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Jacobi;

internal sealed class BranchingHairTreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Jacobi/BranchingHairTree.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual subdivision and hair-tree grafting", H("Actual subdivision and hair-tree grafting"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-graft"),
                DeclarationHandle.Create(Prefix + "graft"), H("Grafting into an actual edge"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any actual cyclic flag graph G, any flag a of G, and any finite open flag structure T : OpenHair, graft subdivides the actual paired edge containing a by a new trivalent vertex and connects T.root to that vertex. The generic definition does not require T to be acyclic. This delivery uses it with T = t.model for a finite ordinary colored binary tree t. Every existing flag, cyclic order and leaf label remains in the graph, including every numbered exterior anchor. The new pairing is explicitly involutive with no fixed point. In particular, the stem of a two-leaf tree has a genuine trivalent parent; an isolated colored Y with no such parent is outside this construction."))), DescribeRole.Definition))));
}
