using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0767Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0767.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0767",
        H("Original frontier context coverage 0767"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-36820", "selected_cut_36820", "Selected cut at depth 10, code 18175, node 979891",
                "At remaining fuel 11 and original index 979891, selection on the full partial prefix of depth 10 and code 18175 returns the complete row with depth 10, base-four code 18175, original node 979891, kind 2, reserved field 0, 17 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-36866", "selected_cut_36866", "Selected cut at depth 12, code 297737, node 895",
                "At remaining fuel 9 and original index 895, selection on the full partial prefix of depth 12 and code 297737 returns the complete row with depth 12, base-four code 297737, original node 895, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-4543-979892", "unmarked_context_9_4543_979892", "Unmarked parent at depth 9, code 4543",
                "The frontier Boolean is false at remaining fuel 12, original node 979892, the whole prefixCache at depth 9 and code 4543, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-74433-982211", "unmarked_context_11_74433_982211", "Unmarked parent at depth 11, code 74433",
                "The frontier Boolean is false at remaining fuel 10, original node 982211, the whole prefixCache at depth 11 and code 74433, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-4543-979892", "node_context_9_4543_979892", "Original split at fuel 12 and node 979892",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 979762, 979844, 979885, 979891. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-74433-982211", "node_context_11_74433_982211", "Original split at fuel 10 and node 982211",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 895, 982086, 982147, 982210. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-18175-979891", "context_10_18175_979891", "Context at depth 10, code 18175, node 979891",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 18175 and original node 979891, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-297737-895", "context_12_297737_895", "Context at depth 12, code 297737, node 895",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 297737 and original node 895, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
