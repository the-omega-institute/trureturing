using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0122Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0122.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0122",
        H("Original frontier context coverage 0122"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-05859", "selected_cut_05859", "Selected cut at depth 14, code 336039, node 179317",
                "At remaining fuel 7 and original index 179317, selection on the full partial prefix of depth 14 and code 336039 returns the complete row with depth 14, base-four code 336039, original node 179317, kind 2, reserved field 0, 1261 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-05905", "selected_cut_05905", "Selected cut at depth 13, code 84052, node 180561",
                "At remaining fuel 8 and original index 180561, selection on the full partial prefix of depth 13 and code 84052 returns the complete row with depth 13, base-four code 84052, original node 180561, kind 2, reserved field 0, 1265 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-84009-179318", "unmarked_context_13_84009_179318", "Unmarked parent at depth 13, code 84009",
                "The frontier Boolean is false at remaining fuel 8, original node 179318, the whole prefixCache at depth 13 and code 84009, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-21012-180545", "unmarked_context_12_21012_180545", "Unmarked parent at depth 12, code 21012",
                "The frontier Boolean is false at remaining fuel 9, original node 180545, the whole prefixCache at depth 12 and code 21012, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-84009-179318", "node_context_13_84009_179318", "Original split at fuel 8 and node 179318",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 179229, 179272, 179296, 179317. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-21012-180545", "node_context_12_21012_180545", "Original split at fuel 9 and node 180545",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 180490, 180518, 180536, 180544. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-14-336039-179317", "context_14_336039_179317", "Context at depth 14, code 336039, node 179317",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 336039 and original node 179317, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-84052-180561", "context_13_84052_180561", "Context at depth 13, code 84052, node 180561",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 84052 and original node 180561, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
