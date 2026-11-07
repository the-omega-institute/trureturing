using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0940Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0940.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0940",
        H("Original frontier context coverage 0940"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-45124", "selected_cut_45124", "Selected cut at depth 11, code 88975, node 977886",
                "At remaining fuel 10 and original index 977886, selection on the full partial prefix of depth 11 and code 88975 returns the complete row with depth 11, base-four code 88975, original node 977886, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-45171", "selected_cut_45171", "Selected cut at depth 11, code 89010, node 1248067",
                "At remaining fuel 10 and original index 1248067, selection on the full partial prefix of depth 11 and code 89010 returns the complete row with depth 11, base-four code 89010, original node 1248067, kind 2, reserved field 0, 1297 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-22243-1246635", "unmarked_context_10_22243_1246635", "Unmarked parent at depth 10, code 22243",
                "The frontier Boolean is false at remaining fuel 11, original node 1246635, the whole prefixCache at depth 10 and code 22243, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-5562-1247983", "unmarked_context_9_5562_1247983", "Unmarked parent at depth 9, code 5562",
                "The frontier Boolean is false at remaining fuel 12, original node 1247983, the whole prefixCache at depth 9 and code 5562, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-22243-1246635", "node_context_10_22243_1246635", "Original split at fuel 11 and node 1246635",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1246381, 1246510, 1246634, 977886. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-5562-1247983", "node_context_9_5562_1247983", "Original split at fuel 12 and node 1247983",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1247604, 1247814, 1247896, 1247982. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-88975-977886", "context_11_88975_977886", "Context at depth 11, code 88975, node 977886",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 88975 and original node 977886, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-89010-1248067", "context_11_89010_1248067", "Context at depth 11, code 89010, node 1248067",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 89010 and original node 1248067, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
