using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0866Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0866.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0866",
        H("Original frontier context coverage 0866"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-41571", "selected_cut_41571", "Selected cut at depth 12, code 336186, node 1136583",
                "At remaining fuel 9 and original index 1136583, selection on the full partial prefix of depth 12 and code 336186 returns the complete row with depth 12, base-four code 336186, original node 1136583, kind 2, reserved field 0, 1769 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-41618", "selected_cut_41618", "Selected cut at depth 11, code 84077, node 1137893",
                "At remaining fuel 10 and original index 1137893, selection on the full partial prefix of depth 11 and code 84077 returns the complete row with depth 11, base-four code 84077, original node 1137893, kind 2, reserved field 0, 1653 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84046-1136608", "unmarked_context_11_84046_1136608", "Unmarked parent at depth 11, code 84046",
                "The frontier Boolean is false at remaining fuel 10, original node 1136608, the whole prefixCache at depth 11 and code 84046, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-21018-1137831", "unmarked_context_10_21018_1137831", "Unmarked parent at depth 10, code 21018",
                "The frontier Boolean is false at remaining fuel 11, original node 1137831, the whole prefixCache at depth 10 and code 21018, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84046-1136608", "node_context_11_84046_1136608", "Original split at fuel 10 and node 1136608",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1136561, 1136583, 1136607. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-21018-1137831", "node_context_10_21018_1137831", "Original split at fuel 11 and node 1137831",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1137780, 1137803, 1109453, 1137830. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-336186-1136583", "context_12_336186_1136583", "Context at depth 12, code 336186, node 1136583",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 336186 and original node 1136583, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-84077-1137893", "context_11_84077_1137893", "Context at depth 11, code 84077, node 1137893",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 84077 and original node 1137893, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
