using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0849Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0849.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0849",
        H("Original frontier context coverage 0849"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-40755", "selected_cut_40755", "Selected cut at depth 12, code 332319, node 1110481",
                "At remaining fuel 9 and original index 1110481, selection on the full partial prefix of depth 12 and code 332319 returns the complete row with depth 12, base-four code 332319, original node 1110481, kind 2, reserved field 0, 2133 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-40801", "selected_cut_40801", "Selected cut at depth 10, code 20776, node 3442",
                "At remaining fuel 11 and original index 3442, selection on the full partial prefix of depth 10 and code 20776 returns the complete row with depth 10, base-four code 20776, original node 3442, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-83079-1110482", "unmarked_context_11_83079_1110482", "Unmarked parent at depth 11, code 83079",
                "The frontier Boolean is false at remaining fuel 10, original node 1110482, the whole prefixCache at depth 11 and code 83079, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-5193-1112147", "unmarked_context_9_5193_1112147", "Unmarked parent at depth 9, code 5193",
                "The frontier Boolean is false at remaining fuel 12, original node 1112147, the whole prefixCache at depth 9 and code 5193, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-83079-1110482", "node_context_11_83079_1110482", "Original split at fuel 10 and node 1110482",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1110392, 1110440, 1110481. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-5193-1112147", "node_context_9_5193_1112147", "Original split at fuel 12 and node 1112147",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 3442, 893098, 1111925, 1112146. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-332319-1110481", "context_12_332319_1110481", "Context at depth 12, code 332319, node 1110481",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 332319 and original node 1110481, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-20776-3442", "context_10_20776_3442", "Context at depth 10, code 20776, node 3442",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 20776 and original node 3442, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
