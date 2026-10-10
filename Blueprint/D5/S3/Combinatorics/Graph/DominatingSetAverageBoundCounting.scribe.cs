using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class DominatingSetAverageBoundCountingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DominatingSetAverageBoundCounting.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The critical-incidence identity and the private-neighbour estimate are Lemmas 2.1 and 2.3 of Iain Beaton and Ben Cameron, A Tight Upper Bound on the Average Order of Dominating Sets of a Graph, arXiv:2208.10475, attributed there to Beaton and Brown.",
        H("Critical Vertices and Private Neighbours"),
        Blocks(
            Node("criticalvertices", "criticalVertices", "Critical vertices", "A member of a dominating set is critical when deleting it produces a set that does not dominate the graph.", DescribeRole.Definition),
            Node("privateneighbors", "privateNeighbors", "Private outside neighbours", "An omitted vertex is private when it has exactly one selected neighbour.", DescribeRole.Definition),
            Node("externallycritical", "externallyCritical", "Externally critical vertices", "A critical selected vertex is externally critical when it has a private neighbour outside the dominating set.", DescribeRole.Definition),
            Node("removable-pairs-eq-omitted-pairs", "removable_pairs_eq_omitted_pairs", "Deletion and insertion", "Deleting a removable selected vertex and inserting an omitted vertex are mutually inverse correspondences between dominating sets differing by one vertex.", DescribeRole.Theorem),
            Node("critical-total-identity", "critical_total_identity", "Critical-incidence identity", "For a finite graph of order n, the sum of the cardinalities of the critical-vertex sets plus n times the number of dominating sets equals twice the sum of the cardinalities of the dominating sets.", DescribeRole.Theorem),
            Node("externallycritical-card-le", "externallyCritical_card_le", "Private-neighbour estimate", "For every finite selected set, the number of externally critical vertices is at most the number of private outside neighbours. Distinct critical vertices cannot share a neighbour having only one selected neighbour.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
