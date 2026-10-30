using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0894Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0894.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0894",
        H("Original frontier context coverage 0894"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-42916", "selected_cut_42916", "Selected cut at depth 12, code 338992, node 1108174",
                "At remaining fuel 9 and original index 1108174, selection on the full partial prefix of depth 12 and code 338992 returns the complete row with depth 12, base-four code 338992, original node 1108174, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-42963", "selected_cut_42963", "Selected cut at depth 12, code 339063, node 1174398",
                "At remaining fuel 9 and original index 1174398, selection on the full partial prefix of depth 12 and code 339063 returns the complete row with depth 12, base-four code 339063, original node 1174398, kind 2, reserved field 0, 1805 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84747-1173118", "unmarked_context_11_84747_1173118", "Unmarked parent at depth 11, code 84747",
                "The frontier Boolean is false at remaining fuel 10, original node 1173118, the whole prefixCache at depth 11 and code 84747, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-84764-1174293", "unmarked_context_11_84764_1174293", "Unmarked parent at depth 11, code 84764",
                "The frontier Boolean is false at remaining fuel 10, original node 1174293, the whole prefixCache at depth 11 and code 84764, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84747-1173118", "node_context_11_84747_1173118", "Original split at fuel 10 and node 1173118",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1173014, 1173066, 1173117. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-84764-1174293", "node_context_11_84764_1174293", "Original split at fuel 10 and node 1174293",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 985390, 1174233, 1174259, 1174292. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-84747-1173118", "context_11_84747_1173118", "Context at depth 11, code 84747, node 1173118",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 84747 and original node 1173118, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_338988_1108174, context_12_338989_1173014, context_12_338990_1173066, context_12_338991_1173117.", DescribeRole.Theorem),
            Node("context-12-339063-1174398", "context_12_339063_1174398", "Context at depth 12, code 339063, node 1174398",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 339063 and original node 1174398, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
