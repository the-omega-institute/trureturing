using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0632Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0632.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0632",
        H("Original frontier context coverage 0632"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-30339", "selected_cut_30339", "Selected cut at depth 13, code 417927, node 765803",
                "At remaining fuel 8 and original index 765803, selection on the full partial prefix of depth 13 and code 417927 returns the complete row with depth 13, base-four code 417927, original node 765803, kind 2, reserved field 0, 873 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-30386", "selected_cut_30386", "Selected cut at depth 12, code 104501, node 767139",
                "At remaining fuel 9 and original index 767139, selection on the full partial prefix of depth 12 and code 104501 returns the complete row with depth 12, base-four code 104501, original node 767139, kind 2, reserved field 0, 4081 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-104481-765804", "unmarked_context_12_104481_765804", "Unmarked parent at depth 12, code 104481",
                "The frontier Boolean is false at remaining fuel 9, original node 765804, the whole prefixCache at depth 12 and code 104481, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-26124-766957", "unmarked_context_11_26124_766957", "Unmarked parent at depth 11, code 26124",
                "The frontier Boolean is false at remaining fuel 10, original node 766957, the whole prefixCache at depth 11 and code 26124, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-104481-765804", "node_context_12_104481_765804", "Original split at fuel 9 and node 765804",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 765743, 765769, 765788, 765803. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-26124-766957", "node_context_11_26124_766957", "Original split at fuel 10 and node 766957",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 766630, 766751, 766844, 766956. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-417927-765803", "context_13_417927_765803", "Context at depth 13, code 417927, node 765803",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 417927 and original node 765803, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-104501-767139", "context_12_104501_767139", "Context at depth 12, code 104501, node 767139",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 104501 and original node 767139, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
