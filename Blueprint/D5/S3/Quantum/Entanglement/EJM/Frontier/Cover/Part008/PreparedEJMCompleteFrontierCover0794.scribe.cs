using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0794Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0794.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0794",
        H("Original frontier context coverage 0794"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-38115", "selected_cut_38115", "Selected cut at depth 12, code 300870, node 1025246",
                "At remaining fuel 9 and original index 1025246, selection on the full partial prefix of depth 12 and code 300870 returns the complete row with depth 12, base-four code 300870, original node 1025246, kind 2, reserved field 0, 2489 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-38162", "selected_cut_38162", "Selected cut at depth 11, code 75233, node 1026684",
                "At remaining fuel 10 and original index 1026684, selection on the full partial prefix of depth 11 and code 75233 returns the complete row with depth 11, base-four code 75233, original node 1026684, kind 2, reserved field 0, 3941 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-75217-1025285", "unmarked_context_11_75217_1025285", "Unmarked parent at depth 11, code 75217",
                "The frontier Boolean is false at remaining fuel 10, original node 1025285, the whole prefixCache at depth 11 and code 75217, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-75232-1026603", "unmarked_context_11_75232_1026603", "Unmarked parent at depth 11, code 75232",
                "The frontier Boolean is false at remaining fuel 10, original node 1026603, the whole prefixCache at depth 11 and code 75232, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-75217-1025285", "node_context_11_75217_1025285", "Original split at fuel 10 and node 1025285",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1025168, 1025203, 1025246, 1025284. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-75232-1026603", "node_context_11_75232_1026603", "Original split at fuel 10 and node 1026603",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1026557, 1026579, 984676, 1026602. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-300870-1025246", "context_12_300870_1025246", "Context at depth 12, code 300870, node 1025246",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 300870 and original node 1025246, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-75233-1026684", "context_11_75233_1026684", "Context at depth 11, code 75233, node 1026684",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 75233 and original node 1026684, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
