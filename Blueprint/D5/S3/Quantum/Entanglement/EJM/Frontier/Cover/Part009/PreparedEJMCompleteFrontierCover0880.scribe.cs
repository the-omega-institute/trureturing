using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0880Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0880.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0880",
        H("Original frontier context coverage 0880"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-42244", "selected_cut_42244", "Selected cut at depth 11, code 84400, node 1154639",
                "At remaining fuel 10 and original index 1154639, selection on the full partial prefix of depth 11 and code 84400 returns the complete row with depth 11, base-four code 84400, original node 1154639, kind 2, reserved field 0, 1541 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-42290", "selected_cut_42290", "Selected cut at depth 12, code 337712, node 1108174",
                "At remaining fuel 9 and original index 1108174, selection on the full partial prefix of depth 12 and code 337712 returns the complete row with depth 12, base-four code 337712, original node 1108174, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-21099-1154620", "unmarked_context_10_21099_1154620", "Unmarked parent at depth 10, code 21099",
                "The frontier Boolean is false at remaining fuel 11, original node 1154620, the whole prefixCache at depth 10 and code 21099, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-21106-1155854", "unmarked_context_10_21106_1155854", "Unmarked parent at depth 10, code 21106",
                "The frontier Boolean is false at remaining fuel 11, original node 1155854, the whole prefixCache at depth 10 and code 21106, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-21099-1154620", "node_context_10_21099_1154620", "Original split at fuel 11 and node 1154620",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1154545, 1154583, 1154604, 1154619. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-21106-1155854", "node_context_10_21106_1155854", "Original split at fuel 11 and node 1155854",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1155582, 1155701, 1155771, 1155853. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-21099-1154620", "context_10_21099_1154620", "Context at depth 10, code 21099, node 1154620",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 21099 and original node 1154620, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_84396_1154545, context_11_84397_1154583, context_11_84398_1154604, context_11_84399_1154619.", DescribeRole.Theorem),
            Node("context-12-337712-1108174", "context_12_337712_1108174", "Context at depth 12, code 337712, node 1108174",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 337712 and original node 1108174, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
