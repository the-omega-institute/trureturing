using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0038Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0038.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0038",
        H("Original frontier context coverage 0038"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-01827", "selected_cut_01827", "Selected cut at depth 12, code 4734, node 61201",
                "At remaining fuel 9 and original index 61201, selection on the full partial prefix of depth 12 and code 4734 returns the complete row with depth 12, base-four code 4734, original node 61201, kind 2, reserved field 0, 3621 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-01874", "selected_cut_01874", "Selected cut at depth 12, code 4778, node 62823",
                "At remaining fuel 9 and original index 62823, selection on the full partial prefix of depth 12 and code 4778 returns the complete row with depth 12, base-four code 4778, original node 62823, kind 2, reserved field 0, 2345 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-1183-61236", "unmarked_context_11_1183_61236", "Unmarked parent at depth 11, code 1183",
                "The frontier Boolean is false at remaining fuel 10, original node 61236, the whole prefixCache at depth 11 and code 1183, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-1193-62734", "unmarked_context_11_1193_62734", "Unmarked parent at depth 11, code 1193",
                "The frontier Boolean is false at remaining fuel 10, original node 62734, the whole prefixCache at depth 11 and code 1193, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-1183-61236", "node_context_11_1183_61236", "Original split at fuel 10 and node 61236",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 61107, 61154, 61201, 61235. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-1193-62734", "node_context_11_1193_62734", "Original split at fuel 10 and node 62734",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 62656, 62684, 62708, 62733. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-4734-61201", "context_12_4734_61201", "Context at depth 12, code 4734, node 61201",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 4734 and original node 61201, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-4778-62823", "context_12_4778_62823", "Context at depth 12, code 4778, node 62823",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 4778 and original node 62823, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
