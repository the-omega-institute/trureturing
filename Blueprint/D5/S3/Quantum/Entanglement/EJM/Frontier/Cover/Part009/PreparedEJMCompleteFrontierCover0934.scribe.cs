using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0934Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0934.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0934",
        H("Original frontier context coverage 0934"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-44836", "selected_cut_44836", "Selected cut at depth 11, code 88795, node 1235979",
                "At remaining fuel 10 and original index 1235979, selection on the full partial prefix of depth 11 and code 88795 returns the complete row with depth 11, base-four code 88795, original node 1235979, kind 2, reserved field 0, 2273 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-44882", "selected_cut_44882", "Selected cut at depth 12, code 355349, node 1172003",
                "At remaining fuel 9 and original index 1172003, selection on the full partial prefix of depth 12 and code 355349 returns the complete row with depth 12, base-four code 355349, original node 1172003, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-22198-1235980", "unmarked_context_10_22198_1235980", "Unmarked parent at depth 10, code 22198",
                "The frontier Boolean is false at remaining fuel 11, original node 1235980, the whole prefixCache at depth 10 and code 22198, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-88836-1237825", "unmarked_context_11_88836_1237825", "Unmarked parent at depth 11, code 88836",
                "The frontier Boolean is false at remaining fuel 10, original node 1237825, the whole prefixCache at depth 11 and code 88836, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-22198-1235980", "node_context_10_22198_1235980", "Original split at fuel 11 and node 1235980",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1235898, 1235948, 900587, 1235979. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-88836-1237825", "node_context_11_88836_1237825", "Original split at fuel 10 and node 1237825",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435160, 1237648, 1237741, 1237824. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-88795-1235979", "context_11_88795_1235979", "Context at depth 11, code 88795, node 1235979",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 88795 and original node 1235979, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-355349-1172003", "context_12_355349_1172003", "Context at depth 12, code 355349, node 1172003",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 355349 and original node 1172003, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
