using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0597Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0597.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0597",
        H("Original frontier context coverage 0597"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-28659", "selected_cut_28659", "Selected cut at depth 11, code 23154, node 722798",
                "At remaining fuel 10 and original index 722798, selection on the full partial prefix of depth 11 and code 23154 returns the complete row with depth 11, base-four code 23154, original node 722798, kind 2, reserved field 0, 3005 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-28706", "selected_cut_28706", "Selected cut at depth 13, code 371780, node 724035",
                "At remaining fuel 8 and original index 724035, selection on the full partial prefix of depth 13 and code 371780 returns the complete row with depth 13, base-four code 371780, original node 724035, kind 2, reserved field 0, 2485 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-5788-722849", "unmarked_context_10_5788_722849", "Unmarked parent at depth 10, code 5788",
                "The frontier Boolean is false at remaining fuel 11, original node 722849, the whole prefixCache at depth 10 and code 5788, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-92944-723995", "unmarked_context_12_92944_723995", "Unmarked parent at depth 12, code 92944",
                "The frontier Boolean is false at remaining fuel 9, original node 723995, the whole prefixCache at depth 12 and code 92944, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-5788-722849", "node_context_10_5788_722849", "Original split at fuel 11 and node 722849",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 722742, 722768, 722798, 722848. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-92944-723995", "node_context_12_92944_723995", "Original split at fuel 9 and node 723995",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 723950, 723972, 723990, 723994. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-23154-722798", "context_11_23154_722798", "Context at depth 11, code 23154, node 722798",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 23154 and original node 722798, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-371780-724035", "context_13_371780_724035", "Context at depth 13, code 371780, node 724035",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 371780 and original node 724035, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
