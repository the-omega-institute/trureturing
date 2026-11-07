using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0127Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0127.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0127",
        H("Original frontier context coverage 0127"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-06098", "selected_cut_06098", "Selected cut at depth 13, code 84248, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 84248 returns the complete row with depth 13, base-four code 84248, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-06146", "selected_cut_06146", "Selected cut at depth 13, code 84326, node 185386",
                "At remaining fuel 8 and original index 185386, selection on the full partial prefix of depth 13 and code 84326 returns the complete row with depth 13, base-four code 84326, original node 185386, kind 2, reserved field 0, 2157 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-21062-184458", "unmarked_context_12_21062_184458", "Unmarked parent at depth 12, code 21062",
                "The frontier Boolean is false at remaining fuel 9, original node 184458, the whole prefixCache at depth 12 and code 21062, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-5269-185301", "unmarked_context_11_5269_185301", "Unmarked parent at depth 11, code 5269",
                "The frontier Boolean is false at remaining fuel 10, original node 185301, the whole prefixCache at depth 11 and code 5269, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-21062-184458", "node_context_12_21062_184458", "Original split at fuel 9 and node 184458",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 184427, 184448, 184457. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-5269-185301", "node_context_11_5269_185301", "Original split at fuel 10 and node 185301",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 185201, 170504, 185249, 185300. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-84248-3444", "context_13_84248_3444", "Context at depth 13, code 84248, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 84248 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-84326-185386", "context_13_84326_185386", "Context at depth 13, code 84326, node 185386",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 84326 and original node 185386, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
