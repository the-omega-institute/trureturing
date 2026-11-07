using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1027Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1027.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1027",
        H("Original frontier context coverage 1027"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-49299", "selected_cut_49299", "Selected cut at depth 12, code 407058, node 1393922",
                "At remaining fuel 9 and original index 1393922, selection on the full partial prefix of depth 12 and code 407058 returns the complete row with depth 12, base-four code 407058, original node 1393922, kind 2, reserved field 0, 2753 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-49347", "selected_cut_49347", "Selected cut at depth 11, code 101790, node 1395534",
                "At remaining fuel 10 and original index 1395534, selection on the full partial prefix of depth 11 and code 101790 returns the complete row with depth 11, base-four code 101790, original node 1395534, kind 2, reserved field 0, 2465 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-101764-1393981", "unmarked_context_11_101764_1393981", "Unmarked parent at depth 11, code 101764",
                "The frontier Boolean is false at remaining fuel 10, original node 1393981, the whole prefixCache at depth 11 and code 101764, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-25446-1395372", "unmarked_context_10_25446_1395372", "Unmarked parent at depth 10, code 25446",
                "The frontier Boolean is false at remaining fuel 11, original node 1395372, the whole prefixCache at depth 10 and code 25446, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-101764-1393981", "node_context_11_101764_1393981", "Original split at fuel 10 and node 1393981",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1393853, 1393922, 1393980. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-25446-1395372", "node_context_10_25446_1395372", "Original split at fuel 11 and node 1395372",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1395233, 1395303, 1369759, 1395371. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-407058-1393922", "context_12_407058_1393922", "Context at depth 12, code 407058, node 1393922",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 407058 and original node 1393922, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-101790-1395534", "context_11_101790_1395534", "Context at depth 11, code 101790, node 1395534",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 101790 and original node 1395534, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
