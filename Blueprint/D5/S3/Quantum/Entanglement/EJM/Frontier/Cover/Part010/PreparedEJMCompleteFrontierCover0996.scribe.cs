using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0996Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0996.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0996",
        H("Original frontier context coverage 0996"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-47811", "selected_cut_47811", "Selected cut at depth 10, code 23397, node 893098",
                "At remaining fuel 11 and original index 893098, selection on the full partial prefix of depth 10 and code 23397 returns the complete row with depth 10, base-four code 23397, original node 893098, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-47859", "selected_cut_47859", "Selected cut at depth 12, code 374553, node 1340338",
                "At remaining fuel 9 and original index 1340338, selection on the full partial prefix of depth 12 and code 374553 returns the complete row with depth 12, base-four code 374553, original node 1340338, kind 2, reserved field 0, 2073 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-93593-1339188", "unmarked_context_11_93593_1339188", "Unmarked parent at depth 11, code 93593",
                "The frontier Boolean is false at remaining fuel 10, original node 1339188, the whole prefixCache at depth 11 and code 93593, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-93636-1340256", "unmarked_context_11_93636_1340256", "Unmarked parent at depth 11, code 93636",
                "The frontier Boolean is false at remaining fuel 10, original node 1340256, the whole prefixCache at depth 11 and code 93636, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-93593-1339188", "node_context_11_93593_1339188", "Original split at fuel 10 and node 1339188",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1339143, 1256866, 1339167, 1339187. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-93636-1340256", "node_context_11_93636_1340256", "Original split at fuel 10 and node 1340256",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1255011, 1340167, 1340213, 1340255. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-23397-893098", "context_10_23397_893098", "Context at depth 10, code 23397, node 893098",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 23397 and original node 893098, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-374553-1340338", "context_12_374553_1340338", "Context at depth 12, code 374553, node 1340338",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 374553 and original node 1340338, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
