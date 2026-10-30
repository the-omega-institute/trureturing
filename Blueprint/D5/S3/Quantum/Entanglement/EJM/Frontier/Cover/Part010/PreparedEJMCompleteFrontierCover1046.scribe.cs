using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1046Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1046.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1046",
        H("Original frontier context coverage 1046"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-50212", "selected_cut_50212", "Selected cut at depth 12, code 423982, node 1431533",
                "At remaining fuel 9 and original index 1431533, selection on the full partial prefix of depth 12 and code 423982 returns the complete row with depth 12, base-four code 423982, original node 1431533, kind 2, reserved field 0, 2241 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-50259", "selected_cut_50259", "Selected cut at depth 12, code 424221, node 1433528",
                "At remaining fuel 9 and original index 1433528, selection on the full partial prefix of depth 12 and code 424221 returns the complete row with depth 12, base-four code 424221, original node 1433528, kind 2, reserved field 0, 1873 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-105995-1431534", "unmarked_context_11_105995_1431534", "Unmarked parent at depth 11, code 105995",
                "The frontier Boolean is false at remaining fuel 10, original node 1431534, the whole prefixCache at depth 11 and code 105995, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-106052-1433399", "unmarked_context_11_106052_1433399", "Unmarked parent at depth 11, code 106052",
                "The frontier Boolean is false at remaining fuel 10, original node 1433399, the whole prefixCache at depth 11 and code 106052, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-105995-1431534", "node_context_11_105995_1431534", "Original split at fuel 10 and node 1431534",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 449505, 1431472, 1431533, 517541. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-106052-1433399", "node_context_11_106052_1433399", "Original split at fuel 10 and node 1433399",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1415033, 1433297, 1433350, 1433398. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-423982-1431533", "context_12_423982_1431533", "Context at depth 12, code 423982, node 1431533",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 423982 and original node 1431533, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-424221-1433528", "context_12_424221_1433528", "Context at depth 12, code 424221, node 1433528",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 424221 and original node 1433528, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
