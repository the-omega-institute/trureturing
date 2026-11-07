using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0318Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0318.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0318",
        H("Original frontier context coverage 0318"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-15267", "selected_cut_15267", "Selected cut at depth 13, code 110748, node 392601",
                "At remaining fuel 8 and original index 392601, selection on the full partial prefix of depth 13 and code 110748 returns the complete row with depth 13, base-four code 110748, original node 392601, kind 2, reserved field 0, 957 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-15315", "selected_cut_15315", "Selected cut at depth 13, code 110799, node 393362",
                "At remaining fuel 8 and original index 393362, selection on the full partial prefix of depth 13 and code 110799 returns the complete row with depth 13, base-four code 110799, original node 393362, kind 2, reserved field 0, 717 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-27687-392659", "unmarked_context_12_27687_392659", "Unmarked parent at depth 12, code 27687",
                "The frontier Boolean is false at remaining fuel 9, original node 392659, the whole prefixCache at depth 12 and code 27687, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-27698-393304", "unmarked_context_12_27698_393304", "Unmarked parent at depth 12, code 27698",
                "The frontier Boolean is false at remaining fuel 9, original node 393304, the whole prefixCache at depth 12 and code 27698, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-27687-392659", "node_context_12_27687_392659", "Original split at fuel 9 and node 392659",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 392601, 392629, 392648, 392658. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-27698-393304", "node_context_12_27698_393304", "Original split at fuel 9 and node 393304",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 393252, 393278, 393297, 393303. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-110748-392601", "context_13_110748_392601", "Context at depth 13, code 110748, node 392601",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 110748 and original node 392601, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-110799-393362", "context_13_110799_393362", "Context at depth 13, code 110799, node 393362",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 110799 and original node 393362, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
