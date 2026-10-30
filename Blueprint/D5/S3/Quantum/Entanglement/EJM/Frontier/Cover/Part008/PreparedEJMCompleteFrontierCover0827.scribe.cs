using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0827Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0827.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0827",
        H("Original frontier context coverage 0827"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-39699", "selected_cut_39699", "Selected cut at depth 13, code 1230930, node 1077154",
                "At remaining fuel 8 and original index 1077154, selection on the full partial prefix of depth 13 and code 1230930 returns the complete row with depth 13, base-four code 1230930, original node 1077154, kind 2, reserved field 0, 1089 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-39746", "selected_cut_39746", "Selected cut at depth 12, code 307760, node 994572",
                "At remaining fuel 9 and original index 994572, selection on the full partial prefix of depth 12 and code 307760 returns the complete row with depth 12, base-four code 307760, original node 994572, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-307732-1077165", "unmarked_context_12_307732_1077165", "Unmarked parent at depth 12, code 307732",
                "The frontier Boolean is false at remaining fuel 9, original node 1077165, the whole prefixCache at depth 12 and code 307732, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-19234-1078371", "unmarked_context_10_19234_1078371", "Unmarked parent at depth 10, code 19234",
                "The frontier Boolean is false at remaining fuel 11, original node 1078371, the whole prefixCache at depth 10 and code 19234, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-307732-1077165", "node_context_12_307732_1077165", "Original split at fuel 9 and node 1077165",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 1077112, 1077135, 1077154, 1077164. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-19234-1078371", "node_context_10_19234_1078371", "Original split at fuel 11 and node 1078371",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1077844, 1078049, 1078169, 1078370. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-1230930-1077154", "context_13_1230930_1077154", "Context at depth 13, code 1230930, node 1077154",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1230930 and original node 1077154, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-307760-994572", "context_12_307760_994572", "Context at depth 12, code 307760, node 994572",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 307760 and original node 994572, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
