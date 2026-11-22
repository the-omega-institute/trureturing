using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.BoundedDegree;

internal sealed class CambieQ19TreeChoicesDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19TreeChoices.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Once the support is fixed, the freedom is to delete one actual edge independently from each fully included cycle.",
        H("Tree subgraphs on each connected support"),
        Blocks(
            Node("cycle-choice", "CycleChoice", "A choice for one cycle restriction",
                "A choice is an optional actual edge of the graph, present precisely when the support contains every vertex.", DescribeRole.Definition),
            Node("deletion-choices", "DeletionChoices", "Independent core and triangle choices",
                "Take the product of the choices for the restrictions of the core cycle and the triangle.", DescribeRole.Definition),
            Node("tree-fiber", "TreeFiber", "The actual tree fiber",
                "A member is an actual tree subgraph of the host whose vertex set equals the specified support.", DescribeRole.Definition),
            Node("tree-fiber-equiv", "treeFiberEquiv", "The tree-fiber equivalence",
                "For every configuration, actual trees on its decoded support correspond bijectively to the independent cycle-edge deletion choices.", DescribeRole.Definition),
            Node("tree-fiber-equiv-edges", "treeFiberEquiv_edges", "Edges in the pruned graph",
                "For every configuration, deletion choice and pair of vertices, the decoded tree contains the edge exactly when the pruned host contains it and both endpoints belong to the support.", DescribeRole.Theorem),
            Node("tree-fiber-equiv-order", "treeFiberEquiv_order", "Pointwise preservation of tree order",
                "Every tree reconstructed from the deletion choices has the vertex count of its support configuration.", DescribeRole.Theorem),
            Node("full-cycle-choice-equiv", "fullCycleChoiceEquiv", "Choices on a full support",
                "The deletion choices on a full vertex support are equivalent to the actual unordered edges of the graph.", DescribeRole.Definition),
            Node("proper-cycle-choice-equiv", "properCycleChoiceEquiv", "Choices on a proper support",
                "When a vertex is missing, the choice type is equivalent to a singleton and its unique element deletes no edge.", DescribeRole.Definition),
            Node("deletion-choices-card", "deletionChoices_card", "Exact tree multiplicity",
                "Multiply a core factor of 5,000 for a full core and one otherwise by a triangle factor of three for a full triangle and one otherwise.", DescribeRole.Theorem),
            Node("deleted-edges", "deletedEdges", "The deleted unordered vertex pairs",
                "Map the selected local edges to unordered pairs of host vertices and take their union.", DescribeRole.Definition),
            Node("tree-fiber-equiv-keeps-edge-iff", "treeFiberEquiv_keeps_edge_iff", "Every remaining induced edge is forced",
                "For every configuration, deletion choice and pair of vertices, the reconstructed tree contains that pair as an edge exactly when it is a host edge, both endpoints lie in the support and the unordered pair is outside the deleted edge set.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration), H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
