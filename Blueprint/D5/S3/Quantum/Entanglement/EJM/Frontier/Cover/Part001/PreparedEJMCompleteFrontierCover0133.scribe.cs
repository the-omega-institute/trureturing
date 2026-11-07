using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0133Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0133.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0133",
        H("Original frontier context coverage 0133"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-06387", "selected_cut_06387", "Selected cut at depth 13, code 86172, node 191476",
                "At remaining fuel 8 and original index 191476, selection on the full partial prefix of depth 13 and code 86172 returns the complete row with depth 13, base-four code 86172, original node 191476, kind 2, reserved field 0, 605 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-06433", "selected_cut_06433", "Selected cut at depth 13, code 86299, node 192611",
                "At remaining fuel 8 and original index 192611, selection on the full partial prefix of depth 13 and code 86299 returns the complete row with depth 13, base-four code 86299, original node 192611, kind 2, reserved field 0, 821 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-21542-191463", "unmarked_context_12_21542_191463", "Unmarked parent at depth 12, code 21542",
                "The frontier Boolean is false at remaining fuel 9, original node 191463, the whole prefixCache at depth 12 and code 21542, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-21574-192612", "unmarked_context_12_21574_192612", "Unmarked parent at depth 12, code 21574",
                "The frontier Boolean is false at remaining fuel 9, original node 192612, the whole prefixCache at depth 12 and code 21574, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-21542-191463", "node_context_12_21542_191463", "Original split at fuel 9 and node 191463",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 191401, 191438, 191452, 191462. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-21574-192612", "node_context_12_21574_192612", "Original split at fuel 9 and node 192612",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 192578, 192599, 192611. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-21542-191463", "context_12_21542_191463", "Context at depth 12, code 21542, node 191463",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 21542 and original node 191463, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_86168_191401, context_13_86169_191438, context_13_86170_191452, context_13_86171_191462.", DescribeRole.Theorem),
            Node("context-12-21574-192612", "context_12_21574_192612", "Context at depth 12, code 21574, node 192612",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 21574 and original node 192612, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_86296_3444, context_13_86297_192578, context_13_86298_192599, context_13_86299_192611.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
