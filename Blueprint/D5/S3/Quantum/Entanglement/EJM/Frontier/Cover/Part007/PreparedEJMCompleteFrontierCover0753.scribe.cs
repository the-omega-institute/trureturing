using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0753Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0753.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0753",
        H("Original frontier context coverage 0753"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-36147", "selected_cut_36147", "Selected cut at depth 13, code 1153059, node 954926",
                "At remaining fuel 8 and original index 954926, selection on the full partial prefix of depth 13 and code 1153059 returns the complete row with depth 13, base-four code 1153059, original node 954926, kind 2, reserved field 0, 841 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-36194", "selected_cut_36194", "Selected cut at depth 12, code 288305, node 956786",
                "At remaining fuel 9 and original index 956786, selection on the full partial prefix of depth 12 and code 288305 returns the complete row with depth 12, base-four code 288305, original node 956786, kind 2, reserved field 0, 2409 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-288264-954927", "unmarked_context_12_288264_954927", "Unmarked parent at depth 12, code 288264",
                "The frontier Boolean is false at remaining fuel 9, original node 954927, the whole prefixCache at depth 12 and code 288264, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-18018-956713", "unmarked_context_10_18018_956713", "Unmarked parent at depth 10, code 18018",
                "The frontier Boolean is false at remaining fuel 11, original node 956713, the whole prefixCache at depth 10 and code 18018, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-288264-954927", "node_context_12_288264_954927", "Original split at fuel 9 and node 954927",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 954846, 954885, 954913, 954926. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-18018-956713", "node_context_10_18018_956713", "Original split at fuel 11 and node 956713",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 956126, 956297, 956484, 956712. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-1153059-954926", "context_13_1153059_954926", "Context at depth 13, code 1153059, node 954926",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1153059 and original node 954926, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-288305-956786", "context_12_288305_956786", "Context at depth 12, code 288305, node 956786",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 288305 and original node 956786, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
