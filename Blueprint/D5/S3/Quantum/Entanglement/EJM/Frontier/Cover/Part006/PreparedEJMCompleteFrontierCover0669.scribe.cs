using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0669Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0669.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0669",
        H("Original frontier context coverage 0669"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-32116", "selected_cut_32116", "Selected cut at depth 13, code 431326, node 824923",
                "At remaining fuel 8 and original index 824923, selection on the full partial prefix of depth 13 and code 431326 returns the complete row with depth 13, base-four code 431326, original node 824923, kind 2, reserved field 0, 1449 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-32162", "selected_cut_32162", "Selected cut at depth 12, code 107846, node 825934",
                "At remaining fuel 9 and original index 825934, selection on the full partial prefix of depth 12 and code 107846 returns the complete row with depth 12, base-four code 107846, original node 825934, kind 2, reserved field 0, 3349 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-107831-824931", "unmarked_context_12_107831_824931", "Unmarked parent at depth 12, code 107831",
                "The frontier Boolean is false at remaining fuel 9, original node 824931, the whole prefixCache at depth 12 and code 107831, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-26960-825835", "unmarked_context_11_26960_825835", "Unmarked parent at depth 11, code 26960",
                "The frontier Boolean is false at remaining fuel 10, original node 825835, the whole prefixCache at depth 11 and code 26960, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-107831-824931", "node_context_12_107831_824931", "Original split at fuel 9 and node 824931",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 824819, 824880, 824923, 824930. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-26960-825835", "node_context_11_26960_825835", "Original split at fuel 10 and node 825835",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 825652, 825706, 825765, 825834. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-431326-824923", "context_13_431326_824923", "Context at depth 13, code 431326, node 824923",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 431326 and original node 824923, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-107846-825934", "context_12_107846_825934", "Context at depth 12, code 107846, node 825934",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 107846 and original node 825934, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
