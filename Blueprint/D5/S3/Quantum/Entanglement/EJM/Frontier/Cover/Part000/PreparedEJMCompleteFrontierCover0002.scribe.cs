using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0002Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0002.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0002",
        H("Original frontier context coverage 0002"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-00098", "selected_cut_00098", "Selected cut at depth 13, code 1070, node 6940",
                "At remaining fuel 8 and original index 6940, selection on the full partial prefix of depth 13 and code 1070 returns the complete row with depth 13, base-four code 1070, original node 6940, kind 2, reserved field 0, 813 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-00144", "selected_cut_00144", "Selected cut at depth 13, code 1152, node 9035",
                "At remaining fuel 8 and original index 9035, selection on the full partial prefix of depth 13 and code 1152 returns the complete row with depth 13, base-four code 1152, original node 9035, kind 2, reserved field 0, 2361 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-267-6966", "unmarked_context_12_267_6966", "Unmarked parent at depth 12, code 267",
                "The frontier Boolean is false at remaining fuel 9, original node 6966, the whole prefixCache at depth 12 and code 267, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-17-8982", "unmarked_context_10_17_8982", "Unmarked parent at depth 10, code 17",
                "The frontier Boolean is false at remaining fuel 11, original node 8982, the whole prefixCache at depth 10 and code 17, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-267-6966", "node_context_12_267_6966", "Original split at fuel 9 and node 6966",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 6786, 6889, 6940, 6965. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-17-8982", "node_context_10_17_8982", "Original split at fuel 11 and node 8982",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 7462, 8032, 8981, 1736. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-1070-6940", "context_13_1070_6940", "Context at depth 13, code 1070, node 6940",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1070 and original node 6940, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-1152-9035", "context_13_1152_9035", "Context at depth 13, code 1152, node 9035",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1152 and original node 9035, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
