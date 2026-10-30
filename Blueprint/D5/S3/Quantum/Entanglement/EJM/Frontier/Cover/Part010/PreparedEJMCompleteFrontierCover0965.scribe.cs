using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0965Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0965.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0965",
        H("Original frontier context coverage 0965"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-46324", "selected_cut_46324", "Selected cut at depth 12, code 370447, node 903806",
                "At remaining fuel 9 and original index 903806, selection on the full partial prefix of depth 12 and code 370447 returns the complete row with depth 12, base-four code 370447, original node 903806, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-46370", "selected_cut_46370", "Selected cut at depth 11, code 92624, node 1283168",
                "At remaining fuel 10 and original index 1283168, selection on the full partial prefix of depth 11 and code 92624 returns the complete row with depth 11, base-four code 92624, original node 1283168, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-92611-1291336", "unmarked_context_11_92611_1291336", "Unmarked parent at depth 11, code 92611",
                "The frontier Boolean is false at remaining fuel 10, original node 1291336, the whole prefixCache at depth 11 and code 92611, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-5788-1292922", "unmarked_context_9_5788_1292922", "Unmarked parent at depth 9, code 5788",
                "The frontier Boolean is false at remaining fuel 12, original node 1292922, the whole prefixCache at depth 9 and code 5788, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-92611-1291336", "node_context_11_92611_1291336", "Original split at fuel 10 and node 1291336",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 1291269, 1291335, 903806. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-5788-1292922", "node_context_9_5788_1292922", "Original split at fuel 12 and node 1292922",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1291337, 1291868, 1292447, 1292921. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-370447-903806", "context_12_370447_903806", "Context at depth 12, code 370447, node 903806",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 370447 and original node 903806, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-92624-1283168", "context_11_92624_1283168", "Context at depth 11, code 92624, node 1283168",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 92624 and original node 1283168, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
