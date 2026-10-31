using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0586Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0586.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0586",
        H("Original frontier context coverage 0586"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-28132", "selected_cut_28132", "Selected cut at depth 11, code 23023, node 710219",
                "At remaining fuel 10 and original index 710219, selection on the full partial prefix of depth 11 and code 23023 returns the complete row with depth 11, base-four code 23023, original node 710219, kind 2, reserved field 0, 2633 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-28178", "selected_cut_28178", "Selected cut at depth 13, code 368714, node 711456",
                "At remaining fuel 8 and original index 711456, selection on the full partial prefix of depth 13 and code 368714 returns the complete row with depth 13, base-four code 368714, original node 711456, kind 2, reserved field 0, 1149 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-5755-710220", "unmarked_context_10_5755_710220", "Unmarked parent at depth 10, code 5755",
                "The frontier Boolean is false at remaining fuel 11, original node 710220, the whole prefixCache at depth 10 and code 5755, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-92177-711397", "unmarked_context_12_92177_711397", "Unmarked parent at depth 12, code 92177",
                "The frontier Boolean is false at remaining fuel 9, original node 711397, the whole prefixCache at depth 12 and code 92177, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-5755-710220", "node_context_10_5755_710220", "Original split at fuel 11 and node 710220",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 710081, 710127, 710185, 710219. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-92177-711397", "node_context_12_92177_711397", "Original split at fuel 9 and node 711397",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 711349, 711371, 711389, 711396. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-23023-710219", "context_11_23023_710219", "Context at depth 11, code 23023, node 710219",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 23023 and original node 710219, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-368714-711456", "context_13_368714_711456", "Context at depth 13, code 368714, node 711456",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 368714 and original node 711456, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
