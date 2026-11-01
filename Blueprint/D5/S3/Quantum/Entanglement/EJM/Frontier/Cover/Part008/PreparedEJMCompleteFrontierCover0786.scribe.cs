using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0786Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0786.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0786",
        H("Original frontier context coverage 0786"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-37731", "selected_cut_37731", "Selected cut at depth 12, code 300297, node 1010898",
                "At remaining fuel 9 and original index 1010898, selection on the full partial prefix of depth 12 and code 300297 returns the complete row with depth 12, base-four code 300297, original node 1010898, kind 2, reserved field 0, 3513 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-37778", "selected_cut_37778", "Selected cut at depth 12, code 300341, node 891951",
                "At remaining fuel 9 and original index 891951, selection on the full partial prefix of depth 12 and code 300341 returns the complete row with depth 12, base-four code 300341, original node 891951, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-300296-1010835", "unmarked_context_12_300296_1010835", "Unmarked parent at depth 12, code 300296",
                "The frontier Boolean is false at remaining fuel 9, original node 1010835, the whole prefixCache at depth 12 and code 300296, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-75084-1012822", "unmarked_context_11_75084_1012822", "Unmarked parent at depth 11, code 75084",
                "The frontier Boolean is false at remaining fuel 10, original node 1012822, the whole prefixCache at depth 11 and code 75084, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-300296-1010835", "node_context_12_300296_1010835", "Original split at fuel 9 and node 1010835",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 1010765, 1010795, 1010825, 1010834. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-75084-1012822", "node_context_11_75084_1012822", "Original split at fuel 10 and node 1012822",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1012693, 1012737, 1012771, 1012821. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-300296-1010835", "context_12_300296_1010835", "Context at depth 12, code 300296, node 1010835",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 300296 and original node 1010835, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_1201184_1010765, context_13_1201185_1010795, context_13_1201186_1010825, context_13_1201187_1010834.", DescribeRole.Theorem),
            Node("context-12-300341-891951", "context_12_300341_891951", "Context at depth 12, code 300341, node 891951",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 300341 and original node 891951, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
