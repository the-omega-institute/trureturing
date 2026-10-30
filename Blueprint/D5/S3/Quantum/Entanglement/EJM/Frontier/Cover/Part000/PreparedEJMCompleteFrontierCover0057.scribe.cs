using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0057Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0057.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0057",
        H("Original frontier context coverage 0057"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-02739", "selected_cut_02739", "Selected cut at depth 13, code 23124, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 23124 returns the complete row with depth 13, base-four code 23124, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-02787", "selected_cut_02787", "Selected cut at depth 12, code 5823, node 86070",
                "At remaining fuel 9 and original index 86070, selection on the full partial prefix of depth 12 and code 5823 returns the complete row with depth 12, base-four code 5823, original node 86070, kind 2, reserved field 0, 1313 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-5780-84919", "unmarked_context_12_5780_84919", "Unmarked parent at depth 12, code 5780",
                "The frontier Boolean is false at remaining fuel 9, original node 84919, the whole prefixCache at depth 12 and code 5780, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-1454-86019", "unmarked_context_11_1454_86019", "Unmarked parent at depth 11, code 1454",
                "The frontier Boolean is false at remaining fuel 10, original node 86019, the whole prefixCache at depth 11 and code 1454, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-5780-84919", "node_context_12_5780_84919", "Original split at fuel 9 and node 84919",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 3444, 84883, 84918. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-1454-86019", "node_context_11_1454_86019", "Original split at fuel 10 and node 86019",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 85939, 85956, 86004, 86018. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-5780-84919", "context_12_5780_84919", "Context at depth 12, code 5780, node 84919",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 5780 and original node 84919, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_23120_3444, context_13_23121_3444, context_13_23122_84883, context_13_23123_84918.", DescribeRole.Theorem),
            Node("context-12-5823-86070", "context_12_5823_86070", "Context at depth 12, code 5823, node 86070",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 5823 and original node 86070, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
