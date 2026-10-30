using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0742Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0742.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0742",
        H("Original frontier context coverage 0742"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-35619", "selected_cut_35619", "Selected cut at depth 12, code 287055, node 937972",
                "At remaining fuel 9 and original index 937972, selection on the full partial prefix of depth 12 and code 287055 returns the complete row with depth 12, base-four code 287055, original node 937972, kind 2, reserved field 0, 2069 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-35665", "selected_cut_35665", "Selected cut at depth 12, code 287119, node 938859",
                "At remaining fuel 9 and original index 938859, selection on the full partial prefix of depth 12 and code 287119 returns the complete row with depth 12, base-four code 287119, original node 938859, kind 2, reserved field 0, 1305 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-71763-937973", "unmarked_context_11_71763_937973", "Unmarked parent at depth 11, code 71763",
                "The frontier Boolean is false at remaining fuel 10, original node 937973, the whole prefixCache at depth 11 and code 71763, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-17944-938861", "unmarked_context_10_17944_938861", "Unmarked parent at depth 10, code 17944",
                "The frontier Boolean is false at remaining fuel 11, original node 938861, the whole prefixCache at depth 10 and code 17944, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-71763-937973", "node_context_11_71763_937973", "Original split at fuel 10 and node 937973",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 937918, 896706, 937943, 937972. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-17944-938861", "node_context_10_17944_938861", "Original split at fuel 11 and node 938861",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 907917, 938687, 938791, 938860. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-287055-937972", "context_12_287055_937972", "Context at depth 12, code 287055, node 937972",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 287055 and original node 937972, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-17944-938861", "context_10_17944_938861", "Context at depth 10, code 17944, node 938861",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 17944 and original node 938861, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_71776_907917, context_11_71777_938687, context_11_71778_938791, context_11_71779_938860.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
