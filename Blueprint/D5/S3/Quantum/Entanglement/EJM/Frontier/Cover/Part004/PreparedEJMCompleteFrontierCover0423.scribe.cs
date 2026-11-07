using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0423Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0423.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0423",
        H("Original frontier context coverage 0423"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-20306", "selected_cut_20306", "Selected cut at depth 13, code 295088, node 520103",
                "At remaining fuel 8 and original index 520103, selection on the full partial prefix of depth 13 and code 295088 returns the complete row with depth 13, base-four code 295088, original node 520103, kind 2, reserved field 0, 197 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-20353", "selected_cut_20353", "Selected cut at depth 12, code 73828, node 4595",
                "At remaining fuel 9 and original index 4595, selection on the full partial prefix of depth 12 and code 73828 returns the complete row with depth 12, base-four code 73828, original node 4595, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-73772-520221", "unmarked_context_12_73772_520221", "Unmarked parent at depth 12, code 73772",
                "The frontier Boolean is false at remaining fuel 9, original node 520221, the whole prefixCache at depth 12 and code 73772, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-18456-522439", "unmarked_context_11_18456_522439", "Unmarked parent at depth 11, code 18456",
                "The frontier Boolean is false at remaining fuel 10, original node 522439, the whole prefixCache at depth 11 and code 18456, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-73772-520221", "node_context_12_73772_520221", "Original split at fuel 9 and node 520221",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 520103, 520165, 520198, 520220. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-18456-522439", "node_context_11_18456_522439", "Original split at fuel 10 and node 522439",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 522297, 522351, 522396, 522438. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-295088-520103", "context_13_295088_520103", "Context at depth 13, code 295088, node 520103",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 295088 and original node 520103, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-73828-4595", "context_12_73828_4595", "Context at depth 12, code 73828, node 4595",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 73828 and original node 4595, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
