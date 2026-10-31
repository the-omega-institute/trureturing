using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0948Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0948.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0948",
        H("Original frontier context coverage 0948"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-45508", "selected_cut_45508", "Selected cut at depth 13, code 1472566, node 1262975",
                "At remaining fuel 8 and original index 1262975, selection on the full partial prefix of depth 13 and code 1472566 returns the complete row with depth 13, base-four code 1472566, original node 1262975, kind 2, reserved field 0, 769 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-45554", "selected_cut_45554", "Selected cut at depth 12, code 368192, node 1173556",
                "At remaining fuel 9 and original index 1173556, selection on the full partial prefix of depth 12 and code 368192 returns the complete row with depth 12, base-four code 368192, original node 1173556, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-368141-1262992", "unmarked_context_12_368141_1262992", "Unmarked parent at depth 12, code 368141",
                "The frontier Boolean is false at remaining fuel 9, original node 1262992, the whole prefixCache at depth 12 and code 368141, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-5752-1265050", "unmarked_context_9_5752_1265050", "Unmarked parent at depth 9, code 5752",
                "The frontier Boolean is false at remaining fuel 12, original node 1265050, the whole prefixCache at depth 9 and code 5752, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-368141-1262992", "node_context_12_368141_1262992", "Original split at fuel 9 and node 1262992",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 1262933, 1262955, 1262975, 1262991. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-5752-1265050", "node_context_9_5752_1265050", "Original split at fuel 12 and node 1265050",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1263155, 1263989, 1264563, 1265049. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-1472566-1262975", "context_13_1472566_1262975", "Context at depth 13, code 1472566, node 1262975",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1472566 and original node 1262975, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-368192-1173556", "context_12_368192_1173556", "Context at depth 12, code 368192, node 1173556",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 368192 and original node 1173556, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
