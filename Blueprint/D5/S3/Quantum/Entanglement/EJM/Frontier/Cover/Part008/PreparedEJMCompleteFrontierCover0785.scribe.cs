using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0785Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0785.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0785",
        H("Original frontier context coverage 0785"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-37683", "selected_cut_37683", "Selected cut at depth 12, code 300156, node 1009444",
                "At remaining fuel 9 and original index 1009444, selection on the full partial prefix of depth 12 and code 300156 returns the complete row with depth 12, base-four code 300156, original node 1009444, kind 2, reserved field 0, 1597 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-37730", "selected_cut_37730", "Selected cut at depth 13, code 1201187, node 1010834",
                "At remaining fuel 8 and original index 1010834, selection on the full partial prefix of depth 13 and code 1201187 returns the complete row with depth 13, base-four code 1201187, original node 1010834, kind 2, reserved field 0, 613 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-75039-1009530", "unmarked_context_11_75039_1009530", "Unmarked parent at depth 11, code 75039",
                "The frontier Boolean is false at remaining fuel 10, original node 1009530, the whole prefixCache at depth 11 and code 75039, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-75073-1010751", "unmarked_context_11_75073_1010751", "Unmarked parent at depth 11, code 75073",
                "The frontier Boolean is false at remaining fuel 10, original node 1010751, the whole prefixCache at depth 11 and code 75073, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-75039-1009530", "node_context_11_75039_1009530", "Original split at fuel 10 and node 1009530",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1009444, 1009469, 1009502, 1009529. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-75073-1010751", "node_context_11_75073_1010751", "Original split at fuel 10 and node 1010751",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1010613, 891951, 1010679, 1010750. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-300156-1009444", "context_12_300156_1009444", "Context at depth 12, code 300156, node 1009444",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 300156 and original node 1009444, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-1201187-1010834", "context_13_1201187_1010834", "Context at depth 13, code 1201187, node 1010834",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1201187 and original node 1010834, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
