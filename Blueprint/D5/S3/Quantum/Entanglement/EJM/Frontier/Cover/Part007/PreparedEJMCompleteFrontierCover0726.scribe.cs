using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0726Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0726.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0726",
        H("Original frontier context coverage 0726"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-34850", "selected_cut_34850", "Selected cut at depth 11, code 70739, node 1736",
                "At remaining fuel 10 and original index 1736, selection on the full partial prefix of depth 11 and code 70739 returns the complete row with depth 11, base-four code 70739, original node 1736, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-34897", "selected_cut_34897", "Selected cut at depth 12, code 283141, node 911781",
                "At remaining fuel 9 and original index 911781, selection on the full partial prefix of depth 12 and code 283141 returns the complete row with depth 12, base-four code 283141, original node 911781, kind 2, reserved field 0, 3045 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-17684-910666", "unmarked_context_10_17684_910666", "Unmarked parent at depth 10, code 17684",
                "The frontier Boolean is false at remaining fuel 11, original node 910666, the whole prefixCache at depth 10 and code 17684, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-283140-911723", "unmarked_context_12_283140_911723", "Unmarked parent at depth 12, code 283140",
                "The frontier Boolean is false at remaining fuel 9, original node 911723, the whole prefixCache at depth 12 and code 283140, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-17684-910666", "node_context_10_17684_910666", "Original split at fuel 11 and node 910666",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 907917, 910569, 910665, 1736. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-283140-911723", "node_context_12_283140_911723", "Original split at fuel 9 and node 911723",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 911665, 911680, 911712, 911722. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-70739-1736", "context_11_70739_1736", "Context at depth 11, code 70739, node 1736",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 70739 and original node 1736, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-283141-911781", "context_12_283141_911781", "Context at depth 12, code 283141, node 911781",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 283141 and original node 911781, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
