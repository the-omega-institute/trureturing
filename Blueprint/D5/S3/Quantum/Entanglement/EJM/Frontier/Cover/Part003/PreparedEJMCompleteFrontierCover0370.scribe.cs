using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0370Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0370.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0370",
        H("Original frontier context coverage 0370"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-17763", "selected_cut_17763", "Selected cut at depth 12, code 70767, node 452466",
                "At remaining fuel 9 and original index 452466, selection on the full partial prefix of depth 12 and code 70767 returns the complete row with depth 12, base-four code 70767, original node 452466, kind 2, reserved field 0, 2821 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-17809", "selected_cut_17809", "Selected cut at depth 14, code 1134673, node 453622",
                "At remaining fuel 7 and original index 453622, selection on the full partial prefix of depth 14 and code 1134673 returns the complete row with depth 14, base-four code 1134673, original node 453622, kind 2, reserved field 0, 1249 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-17691-452467", "unmarked_context_11_17691_452467", "Unmarked parent at depth 11, code 17691",
                "The frontier Boolean is false at remaining fuel 10, original node 452467, the whole prefixCache at depth 11 and code 17691, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-8-276-453482", "unmarked_context_8_276_453482", "Unmarked parent at depth 8, code 276",
                "The frontier Boolean is false at remaining fuel 13, original node 453482, the whole prefixCache at depth 8 and code 276, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-17691-452467", "node_context_11_17691_452467", "Original split at fuel 10 and node 452467",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 452349, 452388, 452429, 452466. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-8-276-453482", "node_context_8_276_453482", "Original split at fuel 13 and node 453482",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 450981, 452469, 453481, 4601. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-70767-452466", "context_12_70767_452466", "Context at depth 12, code 70767, node 452466",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 70767 and original node 452466, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-14-1134673-453622", "context_14_1134673_453622", "Context at depth 14, code 1134673, node 453622",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 1134673 and original node 453622, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
