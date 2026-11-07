using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0283Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0283.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0283",
        H("Original frontier context coverage 0283"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-13586", "selected_cut_13586", "Selected cut at depth 12, code 26768, node 356053",
                "At remaining fuel 9 and original index 356053, selection on the full partial prefix of depth 12 and code 26768 returns the complete row with depth 12, base-four code 26768, original node 356053, kind 2, reserved field 0, 3261 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-13634", "selected_cut_13634", "Selected cut at depth 11, code 6707, node 356952",
                "At remaining fuel 10 and original index 356952, selection on the full partial prefix of depth 11 and code 6707 returns the complete row with depth 11, base-four code 6707, original node 356952, kind 2, reserved field 0, 2909 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-6692-356123", "unmarked_context_11_6692_356123", "Unmarked parent at depth 11, code 6692",
                "The frontier Boolean is false at remaining fuel 10, original node 356123, the whole prefixCache at depth 11 and code 6692, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-418-356821", "unmarked_context_9_418_356821", "Unmarked parent at depth 9, code 418",
                "The frontier Boolean is false at remaining fuel 12, original node 356821, the whole prefixCache at depth 9 and code 418, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-6692-356123", "node_context_11_6692_356123", "Original split at fuel 10 and node 356123",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 356053, 356080, 356102, 356122. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-418-356821", "node_context_9_418_356821", "Original split at fuel 12 and node 356821",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 356003, 356371, 356574, 356820. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-26768-356053", "context_12_26768_356053", "Context at depth 12, code 26768, node 356053",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 26768 and original node 356053, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-6707-356952", "context_11_6707_356952", "Context at depth 11, code 6707, node 356952",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 6707 and original node 356952, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
