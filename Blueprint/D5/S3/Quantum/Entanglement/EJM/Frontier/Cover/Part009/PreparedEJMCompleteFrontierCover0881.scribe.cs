using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0881Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0881.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0881",
        H("Original frontier context coverage 0881"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-42291", "selected_cut_42291", "Selected cut at depth 12, code 337713, node 1155892",
                "At remaining fuel 9 and original index 1155892, selection on the full partial prefix of depth 12 and code 337713 returns the complete row with depth 12, base-four code 337713, original node 1155892, kind 2, reserved field 0, 2545 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-42339", "selected_cut_42339", "Selected cut at depth 12, code 337779, node 1157225",
                "At remaining fuel 9 and original index 1157225, selection on the full partial prefix of depth 12 and code 337779 returns the complete row with depth 12, base-four code 337779, original node 1157225, kind 2, reserved field 0, 2141 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84428-1156009", "unmarked_context_11_84428_1156009", "Unmarked parent at depth 11, code 84428",
                "The frontier Boolean is false at remaining fuel 10, original node 1156009, the whole prefixCache at depth 11 and code 84428, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-21110-1157092", "unmarked_context_10_21110_1157092", "Unmarked parent at depth 10, code 21110",
                "The frontier Boolean is false at remaining fuel 11, original node 1157092, the whole prefixCache at depth 10 and code 21110, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84428-1156009", "node_context_11_84428_1156009", "Original split at fuel 10 and node 1156009",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1155892, 1155947, 1156008. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-21110-1157092", "node_context_10_21110_1157092", "Original split at fuel 11 and node 1157092",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1156885, 1156947, 1157020, 1157091. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-337713-1155892", "context_12_337713_1155892", "Context at depth 12, code 337713, node 1155892",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 337713 and original node 1155892, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-337779-1157225", "context_12_337779_1157225", "Context at depth 12, code 337779, node 1157225",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 337779 and original node 1157225, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
