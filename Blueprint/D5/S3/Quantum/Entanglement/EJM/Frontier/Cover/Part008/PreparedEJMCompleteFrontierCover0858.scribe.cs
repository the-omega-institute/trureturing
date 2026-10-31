using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0858Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0858.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0858",
        H("Original frontier context coverage 0858"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-41187", "selected_cut_41187", "Selected cut at depth 12, code 334407, node 1125658",
                "At remaining fuel 9 and original index 1125658, selection on the full partial prefix of depth 12 and code 334407 returns the complete row with depth 12, base-four code 334407, original node 1125658, kind 2, reserved field 0, 2429 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-41235", "selected_cut_41235", "Selected cut at depth 12, code 334479, node 1126938",
                "At remaining fuel 9 and original index 1126938, selection on the full partial prefix of depth 12 and code 334479 returns the complete row with depth 12, base-four code 334479, original node 1126938, kind 2, reserved field 0, 1057 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-83601-1125659", "unmarked_context_11_83601_1125659", "Unmarked parent at depth 11, code 83601",
                "The frontier Boolean is false at remaining fuel 10, original node 1125659, the whole prefixCache at depth 11 and code 83601, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-83617-1126824", "unmarked_context_11_83617_1126824", "Unmarked parent at depth 11, code 83617",
                "The frontier Boolean is false at remaining fuel 10, original node 1126824, the whole prefixCache at depth 11 and code 83617, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-83601-1125659", "node_context_11_83601_1125659", "Original split at fuel 10 and node 1125659",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1125580, 170504, 1125616, 1125658. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-83617-1126824", "node_context_11_83617_1126824", "Original split at fuel 10 and node 1126824",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1126749, 1126780, 1126803, 1126823. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-334407-1125658", "context_12_334407_1125658", "Context at depth 12, code 334407, node 1125658",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 334407 and original node 1125658, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-334479-1126938", "context_12_334479_1126938", "Context at depth 12, code 334479, node 1126938",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 334479 and original node 1126938, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
