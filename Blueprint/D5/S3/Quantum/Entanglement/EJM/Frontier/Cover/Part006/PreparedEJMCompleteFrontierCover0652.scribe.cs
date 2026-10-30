using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0652Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0652.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0652",
        H("Original frontier context coverage 0652"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-31299", "selected_cut_31299", "Selected cut at depth 12, code 105765, node 772506",
                "At remaining fuel 9 and original index 772506, selection on the full partial prefix of depth 12 and code 105765 returns the complete row with depth 12, base-four code 105765, original node 772506, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-31346", "selected_cut_31346", "Selected cut at depth 12, code 105809, node 775937",
                "At remaining fuel 9 and original index 775937, selection on the full partial prefix of depth 12 and code 105809 returns the complete row with depth 12, base-four code 105809, original node 775937, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-105766-800907", "unmarked_context_12_105766_800907", "Unmarked parent at depth 12, code 105766",
                "The frontier Boolean is false at remaining fuel 9, original node 800907, the whole prefixCache at depth 12 and code 105766, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-1652-803077", "unmarked_context_9_1652_803077", "Unmarked parent at depth 9, code 1652",
                "The frontier Boolean is false at remaining fuel 12, original node 803077, the whole prefixCache at depth 9 and code 1652, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-105766-800907", "node_context_12_105766_800907", "Original split at fuel 9 and node 800907",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 800796, 800830, 800868, 800906. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-1652-803077", "node_context_9_1652_803077", "Original split at fuel 12 and node 803077",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 797446, 800219, 802293, 803076. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-105765-772506", "context_12_105765_772506", "Context at depth 12, code 105765, node 772506",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 105765 and original node 772506, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-105809-775937", "context_12_105809_775937", "Context at depth 12, code 105809, node 775937",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 105809 and original node 775937, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
