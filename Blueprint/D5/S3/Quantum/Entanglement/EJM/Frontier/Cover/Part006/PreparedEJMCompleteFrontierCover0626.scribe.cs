using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0626Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0626.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0626",
        H("Original frontier context coverage 0626"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-30053", "selected_cut_30053", "Selected cut at depth 13, code 375983, node 758774",
                "At remaining fuel 8 and original index 758774, selection on the full partial prefix of depth 13 and code 375983 returns the complete row with depth 13, base-four code 375983, original node 758774, kind 2, reserved field 0, 653 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-30099", "selected_cut_30099", "Selected cut at depth 13, code 376032, node 759527",
                "At remaining fuel 8 and original index 759527, selection on the full partial prefix of depth 13 and code 376032 returns the complete row with depth 13, base-four code 376032, original node 759527, kind 2, reserved field 0, 189 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-93995-758775", "unmarked_context_12_93995_758775", "Unmarked parent at depth 12, code 93995",
                "The frontier Boolean is false at remaining fuel 9, original node 758775, the whole prefixCache at depth 12 and code 93995, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-23501-759523", "unmarked_context_11_23501_759523", "Unmarked parent at depth 11, code 23501",
                "The frontier Boolean is false at remaining fuel 10, original node 759523, the whole prefixCache at depth 11 and code 23501, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-93995-758775", "node_context_12_93995_758775", "Original split at fuel 9 and node 758775",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 758712, 758747, 758769, 758774. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-23501-759523", "node_context_11_23501_759523", "Original split at fuel 10 and node 759523",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 759349, 759406, 759467, 759522. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-375983-758774", "context_13_375983_758774", "Context at depth 13, code 375983, node 758774",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 375983 and original node 758774, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-376032-759527", "context_13_376032_759527", "Context at depth 13, code 376032, node 759527",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 376032 and original node 759527, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
