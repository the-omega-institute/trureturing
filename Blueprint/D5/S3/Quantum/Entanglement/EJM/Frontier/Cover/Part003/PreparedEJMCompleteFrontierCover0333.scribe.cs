using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0333Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0333.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0333",
        H("Original frontier context coverage 0333"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-15988", "selected_cut_15988", "Selected cut at depth 13, code 112015, node 407536",
                "At remaining fuel 8 and original index 407536, selection on the full partial prefix of depth 13 and code 112015 returns the complete row with depth 13, base-four code 112015, original node 407536, kind 2, reserved field 0, 1261 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-16034", "selected_cut_16034", "Selected cut at depth 13, code 112079, node 408375",
                "At remaining fuel 8 and original index 408375, selection on the full partial prefix of depth 13 and code 112079 returns the complete row with depth 13, base-four code 112079, original node 408375, kind 2, reserved field 0, 1005 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-28003-407537", "unmarked_context_12_28003_407537", "Unmarked parent at depth 12, code 28003",
                "The frontier Boolean is false at remaining fuel 9, original node 407537, the whole prefixCache at depth 12 and code 28003, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-7004-408377", "unmarked_context_11_7004_408377", "Unmarked parent at depth 11, code 7004",
                "The frontier Boolean is false at remaining fuel 10, original node 408377, the whole prefixCache at depth 11 and code 7004, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-28003-407537", "node_context_12_28003_407537", "Original split at fuel 9 and node 407537",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 407474, 407517, 407536. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-7004-408377", "node_context_11_7004_408377", "Original split at fuel 10 and node 408377",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 408145, 408252, 408307, 408376. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-112015-407536", "context_13_112015_407536", "Context at depth 13, code 112015, node 407536",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 112015 and original node 407536, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-7004-408377", "context_11_7004_408377", "Context at depth 11, code 7004, node 408377",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 7004 and original node 408377, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_28016_408145, context_12_28017_408252, context_12_28018_408307, context_12_28019_408376.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
