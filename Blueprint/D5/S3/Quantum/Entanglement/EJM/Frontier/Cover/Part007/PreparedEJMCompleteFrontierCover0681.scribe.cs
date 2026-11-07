using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0681Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0681.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0681",
        H("Original frontier context coverage 0681"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-32691", "selected_cut_32691", "Selected cut at depth 13, code 438552, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 438552 returns the complete row with depth 13, base-four code 438552, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-32739", "selected_cut_32739", "Selected cut at depth 12, code 109677, node 842926",
                "At remaining fuel 9 and original index 842926, selection on the full partial prefix of depth 12 and code 109677 returns the complete row with depth 12, base-four code 109677, original node 842926, kind 2, reserved field 0, 3257 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-109638-840923", "unmarked_context_12_109638_840923", "Unmarked parent at depth 12, code 109638",
                "The frontier Boolean is false at remaining fuel 9, original node 840923, the whole prefixCache at depth 12 and code 109638, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-27418-842843", "unmarked_context_11_27418_842843", "Unmarked parent at depth 11, code 27418",
                "The frontier Boolean is false at remaining fuel 10, original node 842843, the whole prefixCache at depth 11 and code 27418, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-109638-840923", "node_context_12_109638_840923", "Original split at fuel 9 and node 840923",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 840890, 840915, 840922. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-27418-842843", "node_context_11_27418_842843", "Original split at fuel 10 and node 842843",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 842727, 842764, 842797, 842842. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-438552-3444", "context_13_438552_3444", "Context at depth 13, code 438552, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 438552 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-109677-842926", "context_12_109677_842926", "Context at depth 12, code 109677, node 842926",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 109677 and original node 842926, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
