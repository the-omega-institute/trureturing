using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Raw.Part000.Raw002Tail442;

internal sealed class NodesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw002Tail442/Nodes.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four exact node equations on the Raw002 Tail442 path",
        H("Four exact node equations on the Raw002 Tail442 path"),
        Blocks(
            Paragraph(Text("These source candidates preserve the original mathematical declarations and proof bodies. Metadata and Scribe preparation alone does not establish kernel acceptance, scoped-report acceptance, emission, complete producer acceptance or a global EJM score bound.")),
            Paragraph(Text("The source file determines declaration GIDs. Existing Lean namespaces and proof attribution are retained; an imported declaration is described by its actual source owner.")),
            Paragraph(Text("The original parent is (13, 5209, 17413); outcomes 3, 3, 3, 3, 2 reach (18, 5335038, 442). These four equations support the intermediate depths 14 through 17. HardSplitCost/NodeReceipt.root_split supplies the separate depth-13 equation. Node equality does not transfer Accepted between different prefixes.")),
            Paragraph(Text("The private intermediate assembly theorems consume these node equations together with all four exact child-context Accepted proofs, and the public raw_cut_00337 result remains the actual downstream Raw declaration.")),
            Node("split-receipt-d14-i17412", "split_receipt_d14_i17412", "Original depth-14 node-17412 receipt",
                "At fuel 7, this checks the actual node against its original coordinate and ordered four child indices; checked_split_node derives the corresponding equation. No prefix-free acceptance is asserted."),
            Node("split-node-d14-i17412", "split_node_d14_i17412", "Original depth-14 node-17412 node",
                "At fuel 7, this is the exact original split-node equation, derived from its checked receipt and used with four complete child-context Accepted proofs. No prefix-free acceptance is asserted."),
            Node("split-receipt-d15-i17411", "split_receipt_d15_i17411", "Original depth-15 node-17411 receipt",
                "At fuel 6, this checks the actual node against its original coordinate and ordered four child indices; checked_split_node derives the corresponding equation. No prefix-free acceptance is asserted."),
            Node("split-node-d15-i17411", "split_node_d15_i17411", "Original depth-15 node-17411 node",
                "At fuel 6, this is the exact original split-node equation, derived from its checked receipt and used with four complete child-context Accepted proofs. No prefix-free acceptance is asserted."),
            Node("split-receipt-d16-i17410", "split_receipt_d16_i17410", "Original depth-16 node-17410 receipt",
                "At fuel 5, this checks the actual node against its original coordinate and ordered four child indices; checked_split_node derives the corresponding equation. No prefix-free acceptance is asserted."),
            Node("split-node-d16-i17410", "split_node_d16_i17410", "Original depth-16 node-17410 node",
                "At fuel 5, this is the exact original split-node equation, derived from its checked receipt and used with four complete child-context Accepted proofs. No prefix-free acceptance is asserted."),
            Node("split-receipt-d17-i1305", "split_receipt_d17_i1305", "Original depth-17 node-1305 receipt",
                "At fuel 4, this checks the actual node against its original coordinate and ordered four child indices; checked_split_node derives the corresponding equation. No prefix-free acceptance is asserted."),
            Node("split-node-d17-i1305", "split_node_d17_i1305", "Original depth-17 node-1305 node",
                "At fuel 4, this is the exact original split-node equation, derived from its checked receipt and used with four complete child-context Accepted proofs. No prefix-free acceptance is asserted."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
