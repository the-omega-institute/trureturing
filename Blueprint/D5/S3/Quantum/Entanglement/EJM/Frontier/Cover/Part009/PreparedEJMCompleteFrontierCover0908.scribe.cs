using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0908Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0908.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0908",
        H("Original frontier context coverage 0908"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-43588", "selected_cut_43588", "Selected cut at depth 12, code 351007, node 903806",
                "At remaining fuel 9 and original index 903806, selection on the full partial prefix of depth 12 and code 351007 returns the complete row with depth 12, base-four code 351007, original node 903806, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-43634", "selected_cut_43634", "Selected cut at depth 11, code 87779, node 1196283",
                "At remaining fuel 10 and original index 1196283, selection on the full partial prefix of depth 11 and code 87779 returns the complete row with depth 11, base-four code 87779, original node 1196283, kind 2, reserved field 0, 2705 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-87751-1194645", "unmarked_context_11_87751_1194645", "Unmarked parent at depth 11, code 87751",
                "The frontier Boolean is false at remaining fuel 10, original node 1194645, the whole prefixCache at depth 11 and code 87751, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-21944-1196284", "unmarked_context_10_21944_1196284", "Unmarked parent at depth 10, code 21944",
                "The frontier Boolean is false at remaining fuel 11, original node 1196284, the whole prefixCache at depth 10 and code 21944, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-87751-1194645", "node_context_11_87751_1194645", "Original split at fuel 10 and node 1194645",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1194539, 1194581, 1194644, 903806. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-21944-1196284", "node_context_10_21944_1196284", "Original split at fuel 11 and node 1196284",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1196163, 1196205, 1196248, 1196283. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-351007-903806", "context_12_351007_903806", "Context at depth 12, code 351007, node 903806",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 351007 and original node 903806, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-21944-1196284", "context_10_21944_1196284", "Context at depth 10, code 21944, node 1196284",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 21944 and original node 1196284, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_87776_1196163, context_11_87777_1196205, context_11_87778_1196248, context_11_87779_1196283.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
