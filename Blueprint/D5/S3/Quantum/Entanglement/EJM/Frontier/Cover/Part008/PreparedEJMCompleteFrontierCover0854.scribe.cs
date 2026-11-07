using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0854Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0854.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0854",
        H("Original frontier context coverage 0854"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-40994", "selected_cut_40994", "Selected cut at depth 12, code 333833, node 1118571",
                "At remaining fuel 9 and original index 1118571, selection on the full partial prefix of depth 12 and code 333833 returns the complete row with depth 12, base-four code 333833, original node 1118571, kind 2, reserved field 0, 2953 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-41042", "selected_cut_41042", "Selected cut at depth 12, code 333884, node 1108174",
                "At remaining fuel 9 and original index 1108174, selection on the full partial prefix of depth 12 and code 333884 returns the complete row with depth 12, base-four code 333884, original node 1108174, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-83458-1118624", "unmarked_context_11_83458_1118624", "Unmarked parent at depth 11, code 83458",
                "The frontier Boolean is false at remaining fuel 10, original node 1118624, the whole prefixCache at depth 11 and code 83458, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-83470-1120478", "unmarked_context_11_83470_1120478", "Unmarked parent at depth 11, code 83470",
                "The frontier Boolean is false at remaining fuel 10, original node 1120478, the whole prefixCache at depth 11 and code 83470, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-83458-1118624", "node_context_11_83458_1118624", "Original split at fuel 10 and node 1118624",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 1118571, 592223, 1118623. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-83470-1120478", "node_context_11_83470_1120478", "Original split at fuel 10 and node 1120478",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1120375, 1120418, 1120477. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-333833-1118571", "context_12_333833_1118571", "Context at depth 12, code 333833, node 1118571",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 333833 and original node 1118571, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-333884-1108174", "context_12_333884_1108174", "Context at depth 12, code 333884, node 1108174",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 333884 and original node 1108174, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
