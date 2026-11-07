using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0217Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0217.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0217",
        H("Original frontier context coverage 0217"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-10418", "selected_cut_10418", "Selected cut at depth 13, code 100388, node 283459",
                "At remaining fuel 8 and original index 283459, selection on the full partial prefix of depth 13 and code 100388 returns the complete row with depth 13, base-four code 100388, original node 283459, kind 2, reserved field 0, 2785 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-10466", "selected_cut_10466", "Selected cut at depth 13, code 100430, node 284545",
                "At remaining fuel 8 and original index 284545, selection on the full partial prefix of depth 13 and code 100430 returns the complete row with depth 13, base-four code 100430, original node 284545, kind 2, reserved field 0, 1309 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-25097-283528", "unmarked_context_12_25097_283528", "Unmarked parent at depth 12, code 25097",
                "The frontier Boolean is false at remaining fuel 9, original node 283528, the whole prefixCache at depth 12 and code 25097, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-25106-284469", "unmarked_context_12_25106_284469", "Unmarked parent at depth 12, code 25106",
                "The frontier Boolean is false at remaining fuel 9, original node 284469, the whole prefixCache at depth 12 and code 25106, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-25097-283528", "node_context_12_25097_283528", "Original split at fuel 9 and node 283528",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 283459, 283497, 283518, 283527. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-25106-284469", "node_context_12_25106_284469", "Original split at fuel 9 and node 284469",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 284424, 284445, 284460, 284468. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-100388-283459", "context_13_100388_283459", "Context at depth 13, code 100388, node 283459",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 100388 and original node 283459, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-100430-284545", "context_13_100430_284545", "Context at depth 13, code 100430, node 284545",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 100430 and original node 284545, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
