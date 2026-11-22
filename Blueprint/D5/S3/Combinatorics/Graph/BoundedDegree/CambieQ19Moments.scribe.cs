using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.BoundedDegree;

internal sealed class CambieQ19MomentsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Moments.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two graph equivalences transport the four moments to sums over the same support configurations with different weights.",
        H("Transporting counts and orders from the actual graph"),
        Blocks(
            Node("subtrees", "Subtrees", "Actual nonempty tree subgraphs",
                "Each element is a host subgraph whose graph on its vertex type is a tree.", DescribeRole.Definition),
            Node("all-trees-equiv", "allTreesEquiv", "Classifying the full tree type",
                "An actual tree of the witness gives its support configuration together with the associated deletion choice.", DescribeRole.Definition),
            Node("inst-fintype-configuration", "instFintypeConfiguration", "Finiteness of the support configurations",
                "The finite enumeration of actual connected supports transports across the support equivalence.", DescribeRole.Definition),
            Node("inst-fintype-deletion-choices", "instFintypeDeletionChoices", "Finiteness of each deletion fiber",
                "Each choice type is finite since the host cycles have finitely many edges.", DescribeRole.Definition),
            Node("connected-count-transport", "connectedCount_transport", "The connected-set count",
                "The connected-support count equals the number of configurations.", DescribeRole.Theorem),
            Node("connected-order-transport", "connectedOrder_transport", "The connected-set order sum",
                "The total connected-set order equals the sum of the decoded order over configurations.", DescribeRole.Theorem),
            Node("subtree-count-transport", "subtreeCount_transport", "The subtree count",
                "The original order-stratified count equals the sum over configurations of their deletion-choice multiplicities.", DescribeRole.Theorem),
            Node("subtree-order-transport", "subtreeOrder_transport", "The subtree order sum",
                "The original order-stratified total order equals the sum of each decoded order multiplied by its deletion-choice multiplicity.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration), H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
