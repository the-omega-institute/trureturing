using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0973Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0973.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0973",
        H("Original frontier context coverage 0973"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-46708", "selected_cut_46708", "Selected cut at depth 11, code 92839, node 1303360",
                "At remaining fuel 10 and original index 1303360, selection on the full partial prefix of depth 11 and code 92839 returns the complete row with depth 11, base-four code 92839, original node 1303360, kind 2, reserved field 0, 1309 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-46755", "selected_cut_46755", "Selected cut at depth 11, code 92874, node 900587",
                "At remaining fuel 10 and original index 900587, selection on the full partial prefix of depth 11 and code 92874 returns the complete row with depth 11, base-four code 92874, original node 900587, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-23209-1303361", "unmarked_context_10_23209_1303361", "Unmarked parent at depth 10, code 23209",
                "The frontier Boolean is false at remaining fuel 11, original node 1303361, the whole prefixCache at depth 10 and code 23209, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-92873-1305025", "unmarked_context_11_92873_1305025", "Unmarked parent at depth 11, code 92873",
                "The frontier Boolean is false at remaining fuel 10, original node 1305025, the whole prefixCache at depth 11 and code 92873, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-23209-1303361", "node_context_10_23209_1303361", "Original split at fuel 11 and node 1303361",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1303300, 1192826, 1303332, 1303360. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-92873-1305025", "node_context_11_92873_1305025", "Original split at fuel 10 and node 1305025",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1304886, 1304938, 1304976, 1305024. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-92839-1303360", "context_11_92839_1303360", "Context at depth 11, code 92839, node 1303360",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 92839 and original node 1303360, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-92874-900587", "context_11_92874_900587", "Context at depth 11, code 92874, node 900587",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 92874 and original node 900587, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
