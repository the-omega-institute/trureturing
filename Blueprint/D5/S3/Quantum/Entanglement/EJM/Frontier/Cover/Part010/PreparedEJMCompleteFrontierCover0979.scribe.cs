using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0979Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0979.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0979",
        H("Original frontier context coverage 0979"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-46995", "selected_cut_46995", "Selected cut at depth 10, code 23253, node 893098",
                "At remaining fuel 11 and original index 893098, selection on the full partial prefix of depth 10 and code 23253 returns the complete row with depth 10, base-four code 23253, original node 893098, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-47043", "selected_cut_47043", "Selected cut at depth 12, code 372243, node 1314777",
                "At remaining fuel 9 and original index 1314777, selection on the full partial prefix of depth 12 and code 372243 returns the complete row with depth 12, base-four code 372243, original node 1314777, kind 2, reserved field 0, 3721 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-93017-1313279", "unmarked_context_11_93017_1313279", "Unmarked parent at depth 11, code 93017",
                "The frontier Boolean is false at remaining fuel 10, original node 1313279, the whole prefixCache at depth 11 and code 93017, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-23264-1314611", "unmarked_context_10_23264_1314611", "Unmarked parent at depth 10, code 23264",
                "The frontier Boolean is false at remaining fuel 11, original node 1314611, the whole prefixCache at depth 10 and code 23264, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-93017-1313279", "node_context_11_93017_1313279", "Original split at fuel 10 and node 1313279",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1313227, 1256866, 1313249, 1313278. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-23264-1314611", "node_context_10_23264_1314611", "Original split at fuel 11 and node 1314611",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 434745, 1314302, 1314445, 1314610. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-23253-893098", "context_10_23253_893098", "Context at depth 10, code 23253, node 893098",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 23253 and original node 893098, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-372243-1314777", "context_12_372243_1314777", "Context at depth 12, code 372243, node 1314777",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 372243 and original node 1314777, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
