using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0912Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0912.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0912",
        H("Original frontier context coverage 0912"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-43779", "selected_cut_43779", "Selected cut at depth 12, code 352527, node 1200515",
                "At remaining fuel 9 and original index 1200515, selection on the full partial prefix of depth 12 and code 352527 returns the complete row with depth 12, base-four code 352527, original node 1200515, kind 2, reserved field 0, 2769 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-43825", "selected_cut_43825", "Selected cut at depth 11, code 88144, node 907917",
                "At remaining fuel 10 and original index 907917, selection on the full partial prefix of depth 11 and code 88144 returns the complete row with depth 11, base-four code 88144, original node 907917, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-88131-1200516", "unmarked_context_11_88131_1200516", "Unmarked parent at depth 11, code 88131",
                "The frontier Boolean is false at remaining fuel 10, original node 1200516, the whole prefixCache at depth 11 and code 88131, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-5508-1202040", "unmarked_context_9_5508_1202040", "Unmarked parent at depth 9, code 5508",
                "The frontier Boolean is false at remaining fuel 12, original node 1202040, the whole prefixCache at depth 9 and code 5508, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-88131-1200516", "node_context_11_88131_1200516", "Original split at fuel 10 and node 1200516",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 1200435, 1200473, 1200515. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-5508-1202040", "node_context_9_5508_1202040", "Original split at fuel 12 and node 1202040",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1200517, 1200983, 1201527, 1202039. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-352527-1200515", "context_12_352527_1200515", "Context at depth 12, code 352527, node 1200515",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 352527 and original node 1200515, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-88144-907917", "context_11_88144_907917", "Context at depth 11, code 88144, node 907917",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 88144 and original node 907917, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
