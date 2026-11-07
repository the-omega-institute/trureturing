using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0286Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0286.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0286",
        H("Original frontier context coverage 0286"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-13730", "selected_cut_13730", "Selected cut at depth 13, code 107600, node 359722",
                "At remaining fuel 8 and original index 359722, selection on the full partial prefix of depth 13 and code 107600 returns the complete row with depth 13, base-four code 107600, original node 359722, kind 2, reserved field 0, 1417 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-13778", "selected_cut_13778", "Selected cut at depth 13, code 107651, node 360567",
                "At remaining fuel 8 and original index 360567, selection on the full partial prefix of depth 13 and code 107651 returns the complete row with depth 13, base-four code 107651, original node 360567, kind 2, reserved field 0, 845 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26900-359769", "unmarked_context_12_26900_359769", "Unmarked parent at depth 12, code 26900",
                "The frontier Boolean is false at remaining fuel 9, original node 359769, the whole prefixCache at depth 12 and code 26900, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-1681-360510", "unmarked_context_10_1681_360510", "Unmarked parent at depth 10, code 1681",
                "The frontier Boolean is false at remaining fuel 11, original node 360510, the whole prefixCache at depth 10 and code 1681, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26900-359769", "node_context_12_26900_359769", "Original split at fuel 9 and node 359769",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 359722, 359745, 359761, 359768. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-1681-360510", "node_context_10_1681_360510", "Original split at fuel 11 and node 360510",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 359705, 359911, 360208, 360509. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-107600-359722", "context_13_107600_359722", "Context at depth 13, code 107600, node 359722",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 107600 and original node 359722, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-107651-360567", "context_13_107651_360567", "Context at depth 13, code 107651, node 360567",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 107651 and original node 360567, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
