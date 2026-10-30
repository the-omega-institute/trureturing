using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0221Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0221.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0221",
        H("Original frontier context coverage 0221"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-10611", "selected_cut_10611", "Selected cut at depth 13, code 100596, node 287091",
                "At remaining fuel 8 and original index 287091, selection on the full partial prefix of depth 13 and code 100596 returns the complete row with depth 13, base-four code 100596, original node 287091, kind 2, reserved field 0, 149 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-10658", "selected_cut_10658", "Selected cut at depth 12, code 25163, node 288095",
                "At remaining fuel 9 and original index 288095, selection on the full partial prefix of depth 12 and code 25163 returns the complete row with depth 12, base-four code 25163, original node 288095, kind 2, reserved field 0, 4065 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-25149-287145", "unmarked_context_12_25149_287145", "Unmarked parent at depth 12, code 25149",
                "The frontier Boolean is false at remaining fuel 9, original node 287145, the whole prefixCache at depth 12 and code 25149, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-25162-288049", "unmarked_context_12_25162_288049", "Unmarked parent at depth 12, code 25162",
                "The frontier Boolean is false at remaining fuel 9, original node 288049, the whole prefixCache at depth 12 and code 25162, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-25149-287145", "node_context_12_25149_287145", "Original split at fuel 9 and node 287145",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 287091, 287119, 287138, 287144. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-25162-288049", "node_context_12_25162_288049", "Original split at fuel 9 and node 288049",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 288025, 288042, 288048. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-100596-287091", "context_13_100596_287091", "Context at depth 13, code 100596, node 287091",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 100596 and original node 287091, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-25163-288095", "context_12_25163_288095", "Context at depth 12, code 25163, node 288095",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25163 and original node 288095, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
