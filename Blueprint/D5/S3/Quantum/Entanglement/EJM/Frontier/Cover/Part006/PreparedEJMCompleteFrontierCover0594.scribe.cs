using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0594Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0594.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0594",
        H("Original frontier context coverage 0594"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-28516", "selected_cut_28516", "Selected cut at depth 13, code 369898, node 719411",
                "At remaining fuel 8 and original index 719411, selection on the full partial prefix of depth 13 and code 369898 returns the complete row with depth 13, base-four code 369898, original node 719411, kind 2, reserved field 0, 1493 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-28562", "selected_cut_28562", "Selected cut at depth 12, code 92501, node 642341",
                "At remaining fuel 9 and original index 642341, selection on the full partial prefix of depth 12 and code 92501 returns the complete row with depth 12, base-four code 92501, original node 642341, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-92474-719420", "unmarked_context_12_92474_719420", "Unmarked parent at depth 12, code 92474",
                "The frontier Boolean is false at remaining fuel 9, original node 719420, the whole prefixCache at depth 12 and code 92474, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-23124-720417", "unmarked_context_11_23124_720417", "Unmarked parent at depth 11, code 23124",
                "The frontier Boolean is false at remaining fuel 10, original node 720417, the whole prefixCache at depth 11 and code 23124, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-92474-719420", "node_context_12_92474_719420", "Original split at fuel 9 and node 719420",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 719370, 719391, 719411, 719419. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-23124-720417", "node_context_11_23124_720417", "Original split at fuel 10 and node 720417",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 720323, 642341, 720369, 720416. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-369898-719411", "context_13_369898_719411", "Context at depth 13, code 369898, node 719411",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 369898 and original node 719411, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-92501-642341", "context_12_92501_642341", "Context at depth 12, code 92501, node 642341",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 92501 and original node 642341, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
