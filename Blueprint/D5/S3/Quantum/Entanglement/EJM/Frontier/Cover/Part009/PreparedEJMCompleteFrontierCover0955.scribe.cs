using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0955Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0955.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0955",
        H("Original frontier context coverage 0955"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-45843", "selected_cut_45843", "Selected cut at depth 12, code 369189, node 1274591",
                "At remaining fuel 9 and original index 1274591, selection on the full partial prefix of depth 12 and code 369189 returns the complete row with depth 12, base-four code 369189, original node 1274591, kind 2, reserved field 0, 3369 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-45891", "selected_cut_45891", "Selected cut at depth 12, code 369267, node 1276195",
                "At remaining fuel 9 and original index 1276195, selection on the full partial prefix of depth 12 and code 369267 returns the complete row with depth 12, base-four code 369267, original node 1276195, kind 2, reserved field 0, 1321 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-92297-1274727", "unmarked_context_11_92297_1274727", "Unmarked parent at depth 11, code 92297",
                "The frontier Boolean is false at remaining fuel 10, original node 1274727, the whole prefixCache at depth 11 and code 92297, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-23078-1276119", "unmarked_context_10_23078_1276119", "Unmarked parent at depth 10, code 23078",
                "The frontier Boolean is false at remaining fuel 11, original node 1276119, the whole prefixCache at depth 10 and code 23078, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-92297-1274727", "node_context_11_92297_1274727", "Original split at fuel 10 and node 1274727",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1274531, 1274591, 1274648, 1274726. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-23078-1276119", "node_context_10_23078_1276119", "Original split at fuel 11 and node 1276119",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1275903, 1275997, 1276028, 1276118. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-369189-1274591", "context_12_369189_1274591", "Context at depth 12, code 369189, node 1274591",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 369189 and original node 1274591, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-369267-1276195", "context_12_369267_1276195", "Context at depth 12, code 369267, node 1276195",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 369267 and original node 1276195, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
