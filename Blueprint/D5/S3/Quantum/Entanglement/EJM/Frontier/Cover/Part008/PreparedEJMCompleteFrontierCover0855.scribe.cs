using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0855Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0855.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0855",
        H("Original frontier context coverage 0855"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-41043", "selected_cut_41043", "Selected cut at depth 12, code 333885, node 1120518",
                "At remaining fuel 9 and original index 1120518, selection on the full partial prefix of depth 12 and code 333885 returns the complete row with depth 12, base-four code 333885, original node 1120518, kind 2, reserved field 0, 2509 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-41089", "selected_cut_41089", "Selected cut at depth 11, code 83488, node 1121776",
                "At remaining fuel 10 and original index 1121776, selection on the full partial prefix of depth 11 and code 83488 returns the complete row with depth 11, base-four code 83488, original node 1121776, kind 2, reserved field 0, 3537 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-83471-1120583", "unmarked_context_11_83471_1120583", "Unmarked parent at depth 11, code 83471",
                "The frontier Boolean is false at remaining fuel 10, original node 1120583, the whole prefixCache at depth 11 and code 83471, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-5217-1121689", "unmarked_context_9_5217_1121689", "Unmarked parent at depth 9, code 5217",
                "The frontier Boolean is false at remaining fuel 12, original node 1121689, the whole prefixCache at depth 9 and code 5217, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-83471-1120583", "node_context_11_83471_1120583", "Original split at fuel 10 and node 1120583",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1120518, 1120581, 1120582. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-5217-1121689", "node_context_9_5217_1121689", "Original split at fuel 12 and node 1121689",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1121003, 893098, 1121339, 1121688. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-333885-1120518", "context_12_333885_1120518", "Context at depth 12, code 333885, node 1120518",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 333885 and original node 1120518, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-83488-1121776", "context_11_83488_1121776", "Context at depth 11, code 83488, node 1121776",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 83488 and original node 1121776, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
