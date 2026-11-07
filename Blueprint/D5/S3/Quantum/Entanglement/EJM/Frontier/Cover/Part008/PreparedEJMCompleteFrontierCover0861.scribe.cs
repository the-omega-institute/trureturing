using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0861Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0861.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0861",
        H("Original frontier context coverage 0861"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-41331", "selected_cut_41331", "Selected cut at depth 12, code 334668, node 1130355",
                "At remaining fuel 9 and original index 1130355, selection on the full partial prefix of depth 12 and code 334668 returns the complete row with depth 12, base-four code 334668, original node 1130355, kind 2, reserved field 0, 1913 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-41378", "selected_cut_41378", "Selected cut at depth 12, code 334739, node 1131593",
                "At remaining fuel 9 and original index 1131593, selection on the full partial prefix of depth 12 and code 334739 returns the complete row with depth 12, base-four code 334739, original node 1131593, kind 2, reserved field 0, 1009 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-83667-1130427", "unmarked_context_11_83667_1130427", "Unmarked parent at depth 11, code 83667",
                "The frontier Boolean is false at remaining fuel 10, original node 1130427, the whole prefixCache at depth 11 and code 83667, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-83684-1131594", "unmarked_context_11_83684_1131594", "Unmarked parent at depth 11, code 83684",
                "The frontier Boolean is false at remaining fuel 10, original node 1131594, the whole prefixCache at depth 11 and code 83684, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-83667-1130427", "node_context_11_83667_1130427", "Original split at fuel 10 and node 1130427",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1130355, 1130386, 1130426, 903806. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-83684-1131594", "node_context_11_83684_1131594", "Original split at fuel 10 and node 1131594",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1131528, 1131546, 1131572, 1131593. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-334668-1130355", "context_12_334668_1130355", "Context at depth 12, code 334668, node 1130355",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 334668 and original node 1130355, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-83684-1131594", "context_11_83684_1131594", "Context at depth 11, code 83684, node 1131594",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 83684 and original node 1131594, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_334736_1131528, context_12_334737_1131546, context_12_334738_1131572, context_12_334739_1131593.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
