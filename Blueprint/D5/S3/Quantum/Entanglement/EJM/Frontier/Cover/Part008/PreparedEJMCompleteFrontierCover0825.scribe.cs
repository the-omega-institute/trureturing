using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0825Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0825.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0825",
        H("Original frontier context coverage 0825"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-39603", "selected_cut_39603", "Selected cut at depth 12, code 307554, node 1074964",
                "At remaining fuel 9 and original index 1074964, selection on the full partial prefix of depth 12 and code 307554 returns the complete row with depth 12, base-four code 307554, original node 1074964, kind 2, reserved field 0, 1593 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-39650", "selected_cut_39650", "Selected cut at depth 11, code 76913, node 1076002",
                "At remaining fuel 10 and original index 1076002, selection on the full partial prefix of depth 11 and code 76913 returns the complete row with depth 11, base-four code 76913, original node 1076002, kind 2, reserved field 0, 1597 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-76888-1074983", "unmarked_context_11_76888_1074983", "Unmarked parent at depth 11, code 76888",
                "The frontier Boolean is false at remaining fuel 10, original node 1074983, the whole prefixCache at depth 11 and code 76888, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-4806-1075981", "unmarked_context_9_4806_1075981", "Unmarked parent at depth 9, code 4806",
                "The frontier Boolean is false at remaining fuel 12, original node 1075981, the whole prefixCache at depth 9 and code 4806, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-76888-1074983", "node_context_11_76888_1074983", "Original split at fuel 10 and node 1074983",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1074929, 1074947, 1074964, 1074982. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-4806-1075981", "node_context_9_4806_1075981", "Original split at fuel 12 and node 1075981",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1075686, 1075823, 1075901, 1075980. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-307554-1074964", "context_12_307554_1074964", "Context at depth 12, code 307554, node 1074964",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 307554 and original node 1074964, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-76913-1076002", "context_11_76913_1076002", "Context at depth 11, code 76913, node 1076002",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 76913 and original node 1076002, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
