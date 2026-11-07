using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0797Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0797.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0797",
        H("Original frontier context coverage 0797"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-38258", "selected_cut_38258", "Selected cut at depth 12, code 301124, node 1030363",
                "At remaining fuel 9 and original index 1030363, selection on the full partial prefix of depth 12 and code 301124 returns the complete row with depth 12, base-four code 301124, original node 1030363, kind 2, reserved field 0, 2437 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-38306", "selected_cut_38306", "Selected cut at depth 12, code 301193, node 1031479",
                "At remaining fuel 9 and original index 1031479, selection on the full partial prefix of depth 12 and code 301193 returns the complete row with depth 12, base-four code 301193, original node 1031479, kind 2, reserved field 0, 1489 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-75281-1030482", "unmarked_context_11_75281_1030482", "Unmarked parent at depth 11, code 75281",
                "The frontier Boolean is false at remaining fuel 10, original node 1030482, the whole prefixCache at depth 11 and code 75281, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-75297-1031431", "unmarked_context_11_75297_1031431", "Unmarked parent at depth 11, code 75297",
                "The frontier Boolean is false at remaining fuel 10, original node 1031431, the whole prefixCache at depth 11 and code 75297, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-75281-1030482", "node_context_11_75281_1030482", "Original split at fuel 10 and node 1030482",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1030363, 1030411, 1030450, 1030481. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-75297-1031431", "node_context_11_75297_1031431", "Original split at fuel 10 and node 1031431",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1031376, 1031402, 984676, 1031430. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-301124-1030363", "context_12_301124_1030363", "Context at depth 12, code 301124, node 1030363",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 301124 and original node 1030363, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-301193-1031479", "context_12_301193_1031479", "Context at depth 12, code 301193, node 1031479",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 301193 and original node 1031479, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
