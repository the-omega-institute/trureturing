using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1028Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1028.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1028",
        H("Original frontier context coverage 1028"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-49348", "selected_cut_49348", "Selected cut at depth 11, code 101791, node 1370051",
                "At remaining fuel 10 and original index 1370051, selection on the full partial prefix of depth 11 and code 101791 returns the complete row with depth 11, base-four code 101791, original node 1370051, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-49394", "selected_cut_49394", "Selected cut at depth 11, code 101840, node 1369428",
                "At remaining fuel 10 and original index 1369428, selection on the full partial prefix of depth 11 and code 101840 returns the complete row with depth 11, base-four code 101840, original node 1369428, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-25447-1395535", "unmarked_context_10_25447_1395535", "Unmarked parent at depth 10, code 25447",
                "The frontier Boolean is false at remaining fuel 11, original node 1395535, the whole prefixCache at depth 10 and code 25447, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-6364-1397201", "unmarked_context_9_6364_1397201", "Unmarked parent at depth 9, code 6364",
                "The frontier Boolean is false at remaining fuel 12, original node 1397201, the whole prefixCache at depth 9 and code 6364, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-25447-1395535", "node_context_10_25447_1395535", "Original split at fuel 11 and node 1395535",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1395437, 1395492, 1395534, 1370051. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-6364-1397201", "node_context_9_6364_1397201", "Original split at fuel 12 and node 1397201",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1396134, 1396514, 1396890, 1397200. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-101791-1370051", "context_11_101791_1370051", "Context at depth 11, code 101791, node 1370051",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 101791 and original node 1370051, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-101840-1369428", "context_11_101840_1369428", "Context at depth 11, code 101840, node 1369428",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 101840 and original node 1369428, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
