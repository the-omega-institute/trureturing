using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0882Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0882.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0882",
        H("Original frontier context coverage 0882"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-42340", "selected_cut_42340", "Selected cut at depth 12, code 337780, node 1157249",
                "At remaining fuel 9 and original index 1157249, selection on the full partial prefix of depth 12 and code 337780 returns the complete row with depth 12, base-four code 337780, original node 1157249, kind 2, reserved field 0, 1453 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-42386", "selected_cut_42386", "Selected cut at depth 12, code 337931, node 1158351",
                "At remaining fuel 9 and original index 1158351, selection on the full partial prefix of depth 12 and code 337931 returns the complete row with depth 12, base-four code 337931, original node 1158351, kind 2, reserved field 0, 2697 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84444-1157226", "unmarked_context_11_84444_1157226", "Unmarked parent at depth 11, code 84444",
                "The frontier Boolean is false at remaining fuel 10, original node 1157226, the whole prefixCache at depth 11 and code 84444, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-84481-1158264", "unmarked_context_11_84481_1158264", "Unmarked parent at depth 11, code 84481",
                "The frontier Boolean is false at remaining fuel 10, original node 1158264, the whole prefixCache at depth 11 and code 84481, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84444-1157226", "node_context_11_84444_1157226", "Original split at fuel 10 and node 1157226",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1157123, 1157149, 1157190, 1157225. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-84481-1158264", "node_context_11_84481_1158264", "Original split at fuel 10 and node 1158264",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 34034, 1158217, 1158263. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-84444-1157226", "context_11_84444_1157226", "Context at depth 11, code 84444, node 1157226",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 84444 and original node 1157226, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_337776_1157123, context_12_337777_1157149, context_12_337778_1157190, context_12_337779_1157225.", DescribeRole.Theorem),
            Node("context-12-337931-1158351", "context_12_337931_1158351", "Context at depth 12, code 337931, node 1158351",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 337931 and original node 1158351, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
