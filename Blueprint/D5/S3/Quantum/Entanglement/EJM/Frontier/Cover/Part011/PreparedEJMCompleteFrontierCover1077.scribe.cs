using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1077Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1077.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1077",
        H("Original frontier context coverage 1077"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-51698", "selected_cut_51698", "Selected cut at depth 10, code 71174, node 1493598",
                "At remaining fuel 11 and original index 1493598, selection on the full partial prefix of depth 10 and code 71174 returns the complete row with depth 10, base-four code 71174, original node 1493598, kind 2, reserved field 0, 3669 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-51746", "selected_cut_51746", "Selected cut at depth 11, code 284825, node 1495682",
                "At remaining fuel 10 and original index 1495682, selection on the full partial prefix of depth 11 and code 284825 returns the complete row with depth 11, base-four code 284825, original node 1495682, kind 2, reserved field 0, 1569 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-17793-1493683", "unmarked_context_9_17793_1493683", "Unmarked parent at depth 9, code 17793",
                "The frontier Boolean is false at remaining fuel 12, original node 1493683, the whole prefixCache at depth 9 and code 17793, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-17800-1495554", "unmarked_context_9_17800_1495554", "Unmarked parent at depth 9, code 17800",
                "The frontier Boolean is false at remaining fuel 12, original node 1495554, the whole prefixCache at depth 9 and code 17800, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-17793-1493683", "node_context_9_17793_1493683", "Original split at fuel 12 and node 1493683",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1493494, 1468874, 1493598, 1493682. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-17800-1495554", "node_context_9_17800_1495554", "Original split at fuel 12 and node 1495554",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1468246, 1495180, 1495346, 1495553. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-71174-1493598", "context_10_71174_1493598", "Context at depth 10, code 71174, node 1493598",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 71174 and original node 1493598, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-284825-1495682", "context_11_284825_1495682", "Context at depth 11, code 284825, node 1495682",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 284825 and original node 1495682, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
