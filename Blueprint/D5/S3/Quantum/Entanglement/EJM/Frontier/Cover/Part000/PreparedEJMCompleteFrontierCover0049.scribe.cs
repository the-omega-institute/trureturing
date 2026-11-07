using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0049Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0049.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0049",
        H("Original frontier context coverage 0049"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-02355", "selected_cut_02355", "Selected cut at depth 13, code 22680, node 76874",
                "At remaining fuel 8 and original index 76874, selection on the full partial prefix of depth 13 and code 22680 returns the complete row with depth 13, base-four code 22680, original node 76874, kind 2, reserved field 0, 1581 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-02402", "selected_cut_02402", "Selected cut at depth 13, code 22727, node 78156",
                "At remaining fuel 8 and original index 78156, selection on the full partial prefix of depth 13 and code 22727 returns the complete row with depth 13, base-four code 22727, original node 78156, kind 2, reserved field 0, 1149 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-5669-76845", "unmarked_context_12_5669_76845", "Unmarked parent at depth 12, code 5669",
                "The frontier Boolean is false at remaining fuel 9, original node 76845, the whole prefixCache at depth 12 and code 5669, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-5680-78057", "unmarked_context_12_5680_78057", "Unmarked parent at depth 12, code 5680",
                "The frontier Boolean is false at remaining fuel 9, original node 78057, the whole prefixCache at depth 12 and code 5680, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-5669-76845", "node_context_12_5669_76845", "Original split at fuel 9 and node 76845",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 76779, 76810, 76834, 76844. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-5680-78057", "node_context_12_5680_78057", "Original split at fuel 9 and node 78057",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 77954, 78005, 78040, 78056. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-5669-76845", "context_12_5669_76845", "Context at depth 12, code 5669, node 76845",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 5669 and original node 76845, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_22676_76779, context_13_22677_76810, context_13_22678_76834, context_13_22679_76844.", DescribeRole.Theorem),
            Node("context-13-22727-78156", "context_13_22727_78156", "Context at depth 13, code 22727, node 78156",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 22727 and original node 78156, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
