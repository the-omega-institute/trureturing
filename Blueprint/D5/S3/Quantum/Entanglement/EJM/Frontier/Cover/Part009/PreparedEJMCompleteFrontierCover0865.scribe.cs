using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0865Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0865.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0865",
        H("Original frontier context coverage 0865"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-41522", "selected_cut_41522", "Selected cut at depth 10, code 21005, node 1135200",
                "At remaining fuel 11 and original index 1135200, selection on the full partial prefix of depth 10 and code 21005 returns the complete row with depth 10, base-four code 21005, original node 1135200, kind 2, reserved field 0, 3725 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-41570", "selected_cut_41570", "Selected cut at depth 12, code 336185, node 1136561",
                "At remaining fuel 9 and original index 1136561, selection on the full partial prefix of depth 12 and code 336185 returns the complete row with depth 12, base-four code 336185, original node 1136561, kind 2, reserved field 0, 2221 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-5251-1135260", "unmarked_context_9_5251_1135260", "Unmarked parent at depth 9, code 5251",
                "The frontier Boolean is false at remaining fuel 12, original node 1135260, the whole prefixCache at depth 9 and code 5251, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-84044-1136456", "unmarked_context_11_84044_1136456", "Unmarked parent at depth 11, code 84044",
                "The frontier Boolean is false at remaining fuel 10, original node 1136456, the whole prefixCache at depth 11 and code 84044, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-5251-1135260", "node_context_9_5251_1135260", "Original split at fuel 12 and node 1135260",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1135155, 1135200, 1135244, 1135259. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-84044-1136456", "node_context_11_84044_1136456", "Original split at fuel 10 and node 1136456",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1136407, 1136429, 1136455. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-21005-1135200", "context_10_21005_1135200", "Context at depth 10, code 21005, node 1135200",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 21005 and original node 1135200, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-336185-1136561", "context_12_336185_1136561", "Context at depth 12, code 336185, node 1136561",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 336185 and original node 1136561, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
