using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0321Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0321.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0321",
        H("Original frontier context coverage 0321"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-15411", "selected_cut_15411", "Selected cut at depth 13, code 110904, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 110904 returns the complete row with depth 13, base-four code 110904, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-15458", "selected_cut_15458", "Selected cut at depth 12, code 27740, node 395893",
                "At remaining fuel 9 and original index 395893, selection on the full partial prefix of depth 12 and code 27740 returns the complete row with depth 12, base-four code 27740, original node 395893, kind 2, reserved field 0, 3649 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-27726-395166", "unmarked_context_12_27726_395166", "Unmarked parent at depth 12, code 27726",
                "The frontier Boolean is false at remaining fuel 9, original node 395166, the whole prefixCache at depth 12 and code 27726, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-6934-395850", "unmarked_context_11_6934_395850", "Unmarked parent at depth 11, code 6934",
                "The frontier Boolean is false at remaining fuel 10, original node 395850, the whole prefixCache at depth 11 and code 6934, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-27726-395166", "node_context_12_27726_395166", "Original split at fuel 9 and node 395166",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 395135, 395155, 395165. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-6934-395850", "node_context_11_6934_395850", "Original split at fuel 10 and node 395850",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 395734, 126371, 395792, 395849. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-110904-3444", "context_13_110904_3444", "Context at depth 13, code 110904, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 110904 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-27740-395893", "context_12_27740_395893", "Context at depth 12, code 27740, node 395893",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 27740 and original node 395893, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
