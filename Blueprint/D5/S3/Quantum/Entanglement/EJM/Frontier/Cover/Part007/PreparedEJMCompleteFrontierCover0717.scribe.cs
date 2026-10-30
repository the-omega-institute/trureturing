using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0717Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0717.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0717",
        H("Original frontier context coverage 0717"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 46 exact cut-selection equations, and 18 literal split equations paired with 18 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-34420", "selected_cut_34420", "Selected cut at depth 11, code 28318, node 891082",
                "At remaining fuel 10 and original index 891082, selection on the full partial prefix of depth 11 and code 28318 returns the complete row with depth 11, base-four code 28318, original node 891082, kind 2, reserved field 0, 965 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-34465", "selected_cut_34465", "Selected cut at depth 12, code 280069, node 893744",
                "At remaining fuel 9 and original index 893744, selection on the full partial prefix of depth 12 and code 280069 returns the complete row with depth 12, base-four code 280069, original node 893744, kind 2, reserved field 0, 1829 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-7079-891104", "unmarked_context_10_7079_891104", "Unmarked parent at depth 10, code 7079",
                "The frontier Boolean is false at remaining fuel 11, original node 891104, the whole prefixCache at depth 10 and code 7079, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-70016-893693", "unmarked_context_11_70016_893693", "Unmarked parent at depth 11, code 70016",
                "The frontier Boolean is false at remaining fuel 10, original node 893693, the whole prefixCache at depth 11 and code 70016, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-7079-891104", "node_context_10_7079_891104", "Original split at fuel 11 and node 891104",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 890976, 891056, 891082, 891103. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-70016-893693", "node_context_11_70016_893693", "Original split at fuel 10 and node 893693",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 893404, 893499, 893599, 893692. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-28318-891082", "context_11_28318_891082", "Context at depth 11, code 28318, node 891082",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 28318 and original node 891082, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-280069-893744", "context_12_280069_893744", "Context at depth 12, code 280069, node 893744",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 280069 and original node 893744, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
