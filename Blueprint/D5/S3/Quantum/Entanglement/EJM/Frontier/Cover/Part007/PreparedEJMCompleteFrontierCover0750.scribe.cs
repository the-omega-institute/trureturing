using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0750Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0750.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0750",
        H("Original frontier context coverage 0750"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-36003", "selected_cut_36003", "Selected cut at depth 12, code 287640, node 949020",
                "At remaining fuel 9 and original index 949020, selection on the full partial prefix of depth 12 and code 287640 returns the complete row with depth 12, base-four code 287640, original node 949020, kind 2, reserved field 0, 1313 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-36049", "selected_cut_36049", "Selected cut at depth 12, code 288016, node 1738",
                "At remaining fuel 9 and original index 1738, selection on the full partial prefix of depth 12 and code 288016 returns the complete row with depth 12, base-four code 288016, original node 1738, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-71910-949069", "unmarked_context_11_71910_949069", "Unmarked parent at depth 11, code 71910",
                "The frontier Boolean is false at remaining fuel 10, original node 949069, the whole prefixCache at depth 11 and code 71910, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-18000-950682", "unmarked_context_10_18000_950682", "Unmarked parent at depth 10, code 18000",
                "The frontier Boolean is false at remaining fuel 11, original node 950682, the whole prefixCache at depth 10 and code 18000, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-71910-949069", "node_context_11_71910_949069", "Original split at fuel 10 and node 949069",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 949020, 949040, 949053, 949068. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-18000-950682", "node_context_10_18000_950682", "Original split at fuel 11 and node 950682",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 949919, 950037, 950397, 950681. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-287640-949020", "context_12_287640_949020", "Context at depth 12, code 287640, node 949020",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 287640 and original node 949020, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-288016-1738", "context_12_288016_1738", "Context at depth 12, code 288016, node 1738",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 288016 and original node 1738, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
