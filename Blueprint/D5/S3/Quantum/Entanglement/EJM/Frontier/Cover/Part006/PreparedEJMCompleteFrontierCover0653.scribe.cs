using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0653Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0653.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0653",
        H("Original frontier context coverage 0653"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-31347", "selected_cut_31347", "Selected cut at depth 12, code 105810, node 803270",
                "At remaining fuel 9 and original index 803270, selection on the full partial prefix of depth 12 and code 105810 returns the complete row with depth 12, base-four code 105810, original node 803270, kind 2, reserved field 0, 2245 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-31394", "selected_cut_31394", "Selected cut at depth 13, code 424001, node 805892",
                "At remaining fuel 8 and original index 805892, selection on the full partial prefix of depth 13 and code 424001 returns the complete row with depth 13, base-four code 424001, original node 805892, kind 2, reserved field 0, 2093 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-26452-803374", "unmarked_context_11_26452_803374", "Unmarked parent at depth 11, code 26452",
                "The frontier Boolean is false at remaining fuel 10, original node 803374, the whole prefixCache at depth 11 and code 26452, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-6624-805818", "unmarked_context_10_6624_805818", "Unmarked parent at depth 10, code 6624",
                "The frontier Boolean is false at remaining fuel 11, original node 805818, the whole prefixCache at depth 10 and code 6624, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-26452-803374", "node_context_11_26452_803374", "Original split at fuel 10 and node 803374",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 803139, 775937, 803270, 803373. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-6624-805818", "node_context_10_6624_805818", "Original split at fuel 11 and node 805818",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 434745, 805369, 805817, 789341. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-105810-803270", "context_12_105810_803270", "Context at depth 12, code 105810, node 803270",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 105810 and original node 803270, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-424001-805892", "context_13_424001_805892", "Context at depth 13, code 424001, node 805892",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 424001 and original node 805892, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
