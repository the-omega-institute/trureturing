using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1026Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1026.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1026",
        H("Original frontier context coverage 1026"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-49252", "selected_cut_49252", "Selected cut at depth 12, code 406831, node 1392372",
                "At remaining fuel 9 and original index 1392372, selection on the full partial prefix of depth 12 and code 406831 returns the complete row with depth 12, base-four code 406831, original node 1392372, kind 2, reserved field 0, 1753 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-49298", "selected_cut_49298", "Selected cut at depth 12, code 407057, node 1393853",
                "At remaining fuel 9 and original index 1393853, selection on the full partial prefix of depth 12 and code 407057 returns the complete row with depth 12, base-four code 407057, original node 1393853, kind 2, reserved field 0, 2417 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-101707-1392373", "unmarked_context_11_101707_1392373", "Unmarked parent at depth 11, code 101707",
                "The frontier Boolean is false at remaining fuel 10, original node 1392373, the whole prefixCache at depth 11 and code 101707, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-25440-1393800", "unmarked_context_10_25440_1393800", "Unmarked parent at depth 10, code 25440",
                "The frontier Boolean is false at remaining fuel 11, original node 1393800, the whole prefixCache at depth 10 and code 25440, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-101707-1392373", "node_context_11_101707_1392373", "Original split at fuel 10 and node 1392373",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1392282, 1392335, 1392372. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-25440-1393800", "node_context_10_25440_1393800", "Original split at fuel 11 and node 1393800",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 434745, 434745, 1393714, 1393799. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-406831-1392372", "context_12_406831_1392372", "Context at depth 12, code 406831, node 1392372",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 406831 and original node 1392372, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-407057-1393853", "context_12_407057_1393853", "Context at depth 12, code 407057, node 1393853",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 407057 and original node 1393853, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
