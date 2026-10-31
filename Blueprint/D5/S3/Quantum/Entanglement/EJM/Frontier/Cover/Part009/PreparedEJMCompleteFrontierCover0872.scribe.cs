using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0872Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0872.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0872",
        H("Original frontier context coverage 0872"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-41859", "selected_cut_41859", "Selected cut at depth 12, code 336786, node 1144105",
                "At remaining fuel 9 and original index 1144105, selection on the full partial prefix of depth 12 and code 336786 returns the complete row with depth 12, base-four code 336786, original node 1144105, kind 2, reserved field 0, 1257 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-41905", "selected_cut_41905", "Selected cut at depth 12, code 336928, node 1108174",
                "At remaining fuel 9 and original index 1108174, selection on the full partial prefix of depth 12 and code 336928 returns the complete row with depth 12, base-four code 336928, original node 1108174, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84196-1144119", "unmarked_context_11_84196_1144119", "Unmarked parent at depth 11, code 84196",
                "The frontier Boolean is false at remaining fuel 10, original node 1144119, the whole prefixCache at depth 11 and code 84196, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-21057-1145580", "unmarked_context_10_21057_1145580", "Unmarked parent at depth 10, code 21057",
                "The frontier Boolean is false at remaining fuel 11, original node 1145580, the whole prefixCache at depth 10 and code 21057, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84196-1144119", "node_context_11_84196_1144119", "Original split at fuel 10 and node 1144119",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1144061, 1144083, 1144105, 1144118. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-21057-1145580", "node_context_10_21057_1145580", "Original split at fuel 11 and node 1145580",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1145303, 892405, 1145435, 1145579. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-336786-1144105", "context_12_336786_1144105", "Context at depth 12, code 336786, node 1144105",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 336786 and original node 1144105, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-336928-1108174", "context_12_336928_1108174", "Context at depth 12, code 336928, node 1108174",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 336928 and original node 1108174, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
