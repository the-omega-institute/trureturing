using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0056Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0056.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0056",
        H("Original frontier context coverage 0056"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-02691", "selected_cut_02691", "Selected cut at depth 13, code 23013, node 83691",
                "At remaining fuel 8 and original index 83691, selection on the full partial prefix of depth 13 and code 23013 returns the complete row with depth 13, base-four code 23013, original node 83691, kind 2, reserved field 0, 461 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-02738", "selected_cut_02738", "Selected cut at depth 13, code 23123, node 84918",
                "At remaining fuel 8 and original index 84918, selection on the full partial prefix of depth 13 and code 23123 returns the complete row with depth 13, base-four code 23123, original node 84918, kind 2, reserved field 0, 1841 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-5753-83745", "unmarked_context_12_5753_83745", "Unmarked parent at depth 12, code 5753",
                "The frontier Boolean is false at remaining fuel 9, original node 83745, the whole prefixCache at depth 12 and code 5753, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-1444-84844", "unmarked_context_11_1444_84844", "Unmarked parent at depth 11, code 1444",
                "The frontier Boolean is false at remaining fuel 10, original node 84844, the whole prefixCache at depth 11 and code 1444, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-5753-83745", "node_context_12_5753_83745", "Original split at fuel 9 and node 83745",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 83691, 83732, 83744. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-1444-84844", "node_context_11_1444_84844", "Original split at fuel 10 and node 84844",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 84743, 84781, 84810, 84843. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-23013-83691", "context_13_23013_83691", "Context at depth 13, code 23013, node 83691",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 23013 and original node 83691, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-23123-84918", "context_13_23123_84918", "Context at depth 13, code 23123, node 84918",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 23123 and original node 84918, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
