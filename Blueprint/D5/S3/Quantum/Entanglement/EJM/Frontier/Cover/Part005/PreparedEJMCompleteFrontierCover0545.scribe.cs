using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0545Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0545.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0545",
        H("Original frontier context coverage 0545"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-26163", "selected_cut_26163", "Selected cut at depth 13, code 354498, node 662006",
                "At remaining fuel 8 and original index 662006, selection on the full partial prefix of depth 13 and code 354498 returns the complete row with depth 13, base-four code 354498, original node 662006, kind 2, reserved field 0, 1297 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-26211", "selected_cut_26211", "Selected cut at depth 13, code 354552, node 662880",
                "At remaining fuel 8 and original index 662880, selection on the full partial prefix of depth 13 and code 354552 returns the complete row with depth 13, base-four code 354552, original node 662880, kind 2, reserved field 0, 93 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-88624-662015", "unmarked_context_12_88624_662015", "Unmarked parent at depth 12, code 88624",
                "The frontier Boolean is false at remaining fuel 9, original node 662015, the whole prefixCache at depth 12 and code 88624, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-88637-662875", "unmarked_context_12_88637_662875", "Unmarked parent at depth 12, code 88637",
                "The frontier Boolean is false at remaining fuel 9, original node 662875, the whole prefixCache at depth 12 and code 88637, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-88624-662015", "node_context_12_88624_662015", "Original split at fuel 9 and node 662015",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 661954, 661988, 662006, 662014. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-88637-662875", "node_context_12_88637_662875", "Original split at fuel 9 and node 662875",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 662820, 662849, 662867, 662874. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-354498-662006", "context_13_354498_662006", "Context at depth 13, code 354498, node 662006",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 354498 and original node 662006, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-354552-662880", "context_13_354552_662880", "Context at depth 13, code 354552, node 662880",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 354552 and original node 662880, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
