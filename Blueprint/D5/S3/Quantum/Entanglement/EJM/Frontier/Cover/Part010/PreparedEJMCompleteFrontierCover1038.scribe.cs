using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1038Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1038.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1038",
        H("Original frontier context coverage 1038"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-49828", "selected_cut_49828", "Selected cut at depth 12, code 409363, node 1413111",
                "At remaining fuel 9 and original index 1413111, selection on the full partial prefix of depth 12 and code 409363 returns the complete row with depth 12, base-four code 409363, original node 1413111, kind 2, reserved field 0, 2505 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-49875", "selected_cut_49875", "Selected cut at depth 9, code 6399, node 1414755",
                "At remaining fuel 12 and original index 1414755, selection on the full partial prefix of depth 9 and code 6399 returns the complete row with depth 9, base-four code 6399, original node 1414755, kind 2, reserved field 0, 2565 subtree occurrences and completion domain 4194304. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-102340-1413112", "unmarked_context_11_102340_1413112", "Unmarked parent at depth 11, code 102340",
                "The frontier Boolean is false at remaining fuel 10, original node 1413112, the whole prefixCache at depth 11 and code 102340, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-6398-1414669", "unmarked_context_9_6398_1414669", "Unmarked parent at depth 9, code 6398",
                "The frontier Boolean is false at remaining fuel 12, original node 1414669, the whole prefixCache at depth 9 and code 6398, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-102340-1413112", "node_context_11_102340_1413112", "Original split at fuel 10 and node 1413112",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1412980, 1413048, 1413111. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-6398-1414669", "node_context_9_6398_1414669", "Original split at fuel 12 and node 1414669",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1414518, 1414597, 1414611, 1414668. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-409363-1413111", "context_12_409363_1413111", "Context at depth 12, code 409363, node 1413111",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 409363 and original node 1413111, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-9-6399-1414755", "context_9_6399_1414755", "Context at depth 9, code 6399, node 1414755",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 6399 and original node 1414755, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
