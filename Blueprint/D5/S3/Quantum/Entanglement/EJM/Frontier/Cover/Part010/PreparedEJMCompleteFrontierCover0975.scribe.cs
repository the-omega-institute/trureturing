using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0975Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0975.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0975",
        H("Original frontier context coverage 0975"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-46804", "selected_cut_46804", "Selected cut at depth 11, code 92896, node 1306406",
                "At remaining fuel 10 and original index 1306406, selection on the full partial prefix of depth 11 and code 92896 returns the complete row with depth 11, base-four code 92896, original node 1306406, kind 2, reserved field 0, 1997 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-46851", "selected_cut_46851", "Selected cut at depth 12, code 371742, node 1308090",
                "At remaining fuel 9 and original index 1308090, selection on the full partial prefix of depth 12 and code 371742 returns the complete row with depth 12, base-four code 371742, original node 1308090, kind 2, reserved field 0, 2825 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-5805-1306371", "unmarked_context_9_5805_1306371", "Unmarked parent at depth 9, code 5805",
                "The frontier Boolean is false at remaining fuel 12, original node 1306371, the whole prefixCache at depth 9 and code 5805, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-92934-1307915", "unmarked_context_11_92934_1307915", "Unmarked parent at depth 11, code 92934",
                "The frontier Boolean is false at remaining fuel 10, original node 1307915, the whole prefixCache at depth 11 and code 92934, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-5805-1306371", "node_context_9_5805_1306371", "Original split at fuel 12 and node 1306371",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1306012, 893098, 1306171, 1306370. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-92934-1307915", "node_context_11_92934_1307915", "Original split at fuel 10 and node 1307915",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 994572, 1307843, 806997, 1307914. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-9-5805-1306371", "context_9_5805_1306371", "Context at depth 9, code 5805, node 1306371",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 5805 and original node 1306371, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_23220_1306012, context_10_23221_893098, context_10_23222_1306171, context_10_23223_1306370.", DescribeRole.Theorem),
            Node("context-12-371742-1308090", "context_12_371742_1308090", "Context at depth 12, code 371742, node 1308090",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 371742 and original node 1308090, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
