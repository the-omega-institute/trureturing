using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0795Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0795.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0795",
        H("Original frontier context coverage 0795"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-38163", "selected_cut_38163", "Selected cut at depth 12, code 300936, node 1026720",
                "At remaining fuel 9 and original index 1026720, selection on the full partial prefix of depth 12 and code 300936 returns the complete row with depth 12, base-four code 300936, original node 1026720, kind 2, reserved field 0, 1549 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-38209", "selected_cut_38209", "Selected cut at depth 12, code 301072, node 985390",
                "At remaining fuel 9 and original index 985390, selection on the full partial prefix of depth 12 and code 301072 returns the complete row with depth 12, base-four code 301072, original node 985390, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-75234-1026771", "unmarked_context_11_75234_1026771", "Unmarked parent at depth 11, code 75234",
                "The frontier Boolean is false at remaining fuel 10, original node 1026771, the whole prefixCache at depth 11 and code 75234, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-18816-1028334", "unmarked_context_10_18816_1028334", "Unmarked parent at depth 10, code 18816",
                "The frontier Boolean is false at remaining fuel 11, original node 1028334, the whole prefixCache at depth 10 and code 18816, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-75234-1026771", "node_context_11_75234_1026771", "Original split at fuel 10 and node 1026771",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1026720, 1026742, 984676, 1026770. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-18816-1028334", "node_context_10_18816_1028334", "Original split at fuel 11 and node 1028334",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1027544, 1027842, 1028051, 1028333. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-300936-1026720", "context_12_300936_1026720", "Context at depth 12, code 300936, node 1026720",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 300936 and original node 1026720, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-301072-985390", "context_12_301072_985390", "Context at depth 12, code 301072, node 985390",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 301072 and original node 985390, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
