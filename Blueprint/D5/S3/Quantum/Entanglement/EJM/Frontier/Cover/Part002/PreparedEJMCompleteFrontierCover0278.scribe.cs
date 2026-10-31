using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0278Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0278.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0278",
        H("Original frontier context coverage 0278"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-13347", "selected_cut_13347", "Selected cut at depth 13, code 106677, node 351321",
                "At remaining fuel 8 and original index 351321, selection on the full partial prefix of depth 13 and code 106677 returns the complete row with depth 13, base-four code 106677, original node 351321, kind 2, reserved field 0, 1901 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-13394", "selected_cut_13394", "Selected cut at depth 13, code 106724, node 351984",
                "At remaining fuel 8 and original index 351984, selection on the full partial prefix of depth 13 and code 106724 returns the complete row with depth 13, base-four code 106724, original node 351984, kind 2, reserved field 0, 269 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26669-351342", "unmarked_context_12_26669_351342", "Unmarked parent at depth 12, code 26669",
                "The frontier Boolean is false at remaining fuel 9, original node 351342, the whole prefixCache at depth 12 and code 26669, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-26680-351980", "unmarked_context_12_26680_351980", "Unmarked parent at depth 12, code 26680",
                "The frontier Boolean is false at remaining fuel 9, original node 351980, the whole prefixCache at depth 12 and code 26680, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26669-351342", "node_context_12_26669_351342", "Original split at fuel 9 and node 351342",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 351298, 351321, 351337, 351341. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-26680-351980", "node_context_12_26680_351980", "Original split at fuel 9 and node 351980",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 351925, 351954, 351972, 351979. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-106677-351321", "context_13_106677_351321", "Context at depth 13, code 106677, node 351321",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 106677 and original node 351321, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-106724-351984", "context_13_106724_351984", "Context at depth 13, code 106724, node 351984",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 106724 and original node 351984, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
