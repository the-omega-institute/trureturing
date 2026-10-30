using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0868Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0868.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0868",
        H("Original frontier context coverage 0868"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-41667", "selected_cut_41667", "Selected cut at depth 12, code 336429, node 1139224",
                "At remaining fuel 9 and original index 1139224, selection on the full partial prefix of depth 12 and code 336429 returns the complete row with depth 12, base-four code 336429, original node 1139224, kind 2, reserved field 0, 2361 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-41714", "selected_cut_41714", "Selected cut at depth 12, code 336497, node 1140333",
                "At remaining fuel 9 and original index 1140333, selection on the full partial prefix of depth 12 and code 336497 returns the complete row with depth 12, base-four code 336497, original node 1140333, kind 2, reserved field 0, 1309 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84107-1139274", "unmarked_context_11_84107_1139274", "Unmarked parent at depth 11, code 84107",
                "The frontier Boolean is false at remaining fuel 10, original node 1139274, the whole prefixCache at depth 11 and code 84107, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-21030-1140299", "unmarked_context_10_21030_1140299", "Unmarked parent at depth 10, code 21030",
                "The frontier Boolean is false at remaining fuel 11, original node 1140299, the whole prefixCache at depth 10 and code 21030, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84107-1139274", "node_context_11_84107_1139274", "Original split at fuel 10 and node 1139274",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1139224, 1139247, 1139273. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-21030-1140299", "node_context_10_21030_1140299", "Original split at fuel 11 and node 1140299",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1140036, 1140114, 1140211, 1140298. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-336429-1139224", "context_12_336429_1139224", "Context at depth 12, code 336429, node 1139224",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 336429 and original node 1139224, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-336497-1140333", "context_12_336497_1140333", "Context at depth 12, code 336497, node 1140333",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 336497 and original node 1140333, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
