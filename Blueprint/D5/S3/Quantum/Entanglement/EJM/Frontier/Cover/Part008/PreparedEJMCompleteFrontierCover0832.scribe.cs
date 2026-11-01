using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0832Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0832.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0832",
        H("Original frontier context coverage 0832"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 46 exact cut-selection equations, and 18 literal split equations paired with 18 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-39940", "selected_cut_39940", "Selected cut at depth 12, code 308077, node 1084266",
                "At remaining fuel 9 and original index 1084266, selection on the full partial prefix of depth 12 and code 308077 returns the complete row with depth 12, base-four code 308077, original node 1084266, kind 2, reserved field 0, 1857 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-39985", "selected_cut_39985", "Selected cut at depth 8, code 1204, node 979897",
                "At remaining fuel 13 and original index 979897, selection on the full partial prefix of depth 8 and code 1204 returns the complete row with depth 8, base-four code 1204, original node 979897, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16777216. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-77019-1084295", "unmarked_context_11_77019_1084295", "Unmarked parent at depth 11, code 77019",
                "The frontier Boolean is false at remaining fuel 10, original node 1084295, the whole prefixCache at depth 11 and code 77019, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-7-300-1085252", "unmarked_context_7_300_1085252", "Unmarked parent at depth 7, code 300",
                "The frontier Boolean is false at remaining fuel 14, original node 1085252, the whole prefixCache at depth 7 and code 300, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-77019-1084295", "node_context_11_77019_1084295", "Original split at fuel 10 and node 1084295",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1084234, 1084266, 1084294, 903806. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-7-300-1085252", "node_context_7_300_1085252", "Original split at fuel 14 and node 1085252",
                "The complete original decoder output is the split at coordinate 7, with value children 0 through 3 respectively at original indices 1072442, 1076200, 1080974, 1085251. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-308077-1084266", "context_12_308077_1084266", "Context at depth 12, code 308077, node 1084266",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 308077 and original node 1084266, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-8-1204-979897", "context_8_1204_979897", "Context at depth 8, code 1204, node 979897",
                "The conclusion is adaptive Accepted at the exact depth 8, full base-four code 1204 and original node 979897, hence remaining fuel 13, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
