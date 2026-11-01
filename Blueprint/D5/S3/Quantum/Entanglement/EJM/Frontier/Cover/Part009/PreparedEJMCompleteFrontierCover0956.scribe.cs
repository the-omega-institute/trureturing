using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0956Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0956.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0956",
        H("Original frontier context coverage 0956"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-45892", "selected_cut_45892", "Selected cut at depth 11, code 92317, node 1276261",
                "At remaining fuel 10 and original index 1276261, selection on the full partial prefix of depth 11 and code 92317 returns the complete row with depth 11, base-four code 92317, original node 1276261, kind 2, reserved field 0, 3701 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-45938", "selected_cut_45938", "Selected cut at depth 12, code 369440, node 435790",
                "At remaining fuel 9 and original index 435790, selection on the full partial prefix of depth 12 and code 369440 returns the complete row with depth 12, base-four code 369440, original node 435790, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-92316-1276196", "unmarked_context_11_92316_1276196", "Unmarked parent at depth 11, code 92316",
                "The frontier Boolean is false at remaining fuel 10, original node 1276196, the whole prefixCache at depth 11 and code 92316, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-23089-1277956", "unmarked_context_10_23089_1277956", "Unmarked parent at depth 10, code 23089",
                "The frontier Boolean is false at remaining fuel 11, original node 1277956, the whole prefixCache at depth 10 and code 23089, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-92316-1276196", "node_context_11_92316_1276196", "Original split at fuel 10 and node 1276196",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1276139, 1276160, 1276171, 1276195. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-23089-1277956", "node_context_10_23089_1277956", "Original split at fuel 11 and node 1277956",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1277518, 815620, 1277783, 1277955. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-92316-1276196", "context_11_92316_1276196", "Context at depth 11, code 92316, node 1276196",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 92316 and original node 1276196, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_369264_1276139, context_12_369265_1276160, context_12_369266_1276171, context_12_369267_1276195.", DescribeRole.Theorem),
            Node("context-12-369440-435790", "context_12_369440_435790", "Context at depth 12, code 369440, node 435790",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 369440 and original node 435790, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
