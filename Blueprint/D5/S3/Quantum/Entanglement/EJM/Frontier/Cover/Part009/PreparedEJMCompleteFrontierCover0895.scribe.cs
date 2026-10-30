using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0895Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0895.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0895",
        H("Original frontier context coverage 0895"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-42964", "selected_cut_42964", "Selected cut at depth 12, code 339064, node 1174420",
                "At remaining fuel 9 and original index 1174420, selection on the full partial prefix of depth 12 and code 339064 returns the complete row with depth 12, base-four code 339064, original node 1174420, kind 2, reserved field 0, 1221 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-43010", "selected_cut_43010", "Selected cut at depth 12, code 339218, node 1175993",
                "At remaining fuel 9 and original index 1175993, selection on the full partial prefix of depth 12 and code 339218 returns the complete row with depth 12, base-four code 339218, original node 1175993, kind 2, reserved field 0, 2589 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84765-1174399", "unmarked_context_11_84765_1174399", "Unmarked parent at depth 11, code 84765",
                "The frontier Boolean is false at remaining fuel 10, original node 1174399, the whole prefixCache at depth 11 and code 84765, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-21200-1175873", "unmarked_context_10_21200_1175873", "Unmarked parent at depth 10, code 21200",
                "The frontier Boolean is false at remaining fuel 11, original node 1175873, the whole prefixCache at depth 10 and code 21200, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84765-1174399", "node_context_11_84765_1174399", "Original split at fuel 10 and node 1174399",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1174324, 642794, 1174355, 1174398. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-21200-1175873", "node_context_10_21200_1175873", "Original split at fuel 11 and node 1175873",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 434745, 1175590, 1175777, 1175872. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-84765-1174399", "context_11_84765_1174399", "Context at depth 11, code 84765, node 1174399",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 84765 and original node 1174399, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_339060_1174324, context_12_339061_642794, context_12_339062_1174355, context_12_339063_1174398.", DescribeRole.Theorem),
            Node("context-12-339218-1175993", "context_12_339218_1175993", "Context at depth 12, code 339218, node 1175993",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 339218 and original node 1175993, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
