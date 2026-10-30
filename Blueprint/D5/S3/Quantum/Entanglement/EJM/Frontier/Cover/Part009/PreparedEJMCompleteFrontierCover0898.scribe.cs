using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0898Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0898.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0898",
        H("Original frontier context coverage 0898"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-43107", "selected_cut_43107", "Selected cut at depth 11, code 84837, node 1178271",
                "At remaining fuel 10 and original index 1178271, selection on the full partial prefix of depth 11 and code 84837 returns the complete row with depth 11, base-four code 84837, original node 1178271, kind 2, reserved field 0, 1905 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-43154", "selected_cut_43154", "Selected cut at depth 12, code 339488, node 1108174",
                "At remaining fuel 9 and original index 1108174, selection on the full partial prefix of depth 12 and code 339488 returns the complete row with depth 12, base-four code 339488, original node 1108174, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-21209-1178379", "unmarked_context_10_21209_1178379", "Unmarked parent at depth 10, code 21209",
                "The frontier Boolean is false at remaining fuel 11, original node 1178379, the whole prefixCache at depth 10 and code 21209, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-21217-1179816", "unmarked_context_10_21217_1179816", "Unmarked parent at depth 10, code 21217",
                "The frontier Boolean is false at remaining fuel 11, original node 1179816, the whole prefixCache at depth 10 and code 21217, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-21209-1178379", "node_context_10_21209_1178379", "Original split at fuel 11 and node 1178379",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1178238, 1178271, 1178313, 1178378. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-21217-1179816", "node_context_10_21217_1179816", "Original split at fuel 11 and node 1179816",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1179456, 1179576, 1179684, 1179815. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-84837-1178271", "context_11_84837_1178271", "Context at depth 11, code 84837, node 1178271",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 84837 and original node 1178271, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-339488-1108174", "context_12_339488_1108174", "Context at depth 12, code 339488, node 1108174",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 339488 and original node 1108174, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
