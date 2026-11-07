using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0638Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0638.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0638",
        H("Original frontier context coverage 0638"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-30627", "selected_cut_30627", "Selected cut at depth 13, code 419910, node 778027",
                "At remaining fuel 8 and original index 778027, selection on the full partial prefix of depth 13 and code 419910 returns the complete row with depth 13, base-four code 419910, original node 778027, kind 2, reserved field 0, 1349 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-30675", "selected_cut_30675", "Selected cut at depth 13, code 419961, node 779193",
                "At remaining fuel 8 and original index 779193, selection on the full partial prefix of depth 13 and code 419961 returns the complete row with depth 13, base-four code 419961, original node 779193, kind 2, reserved field 0, 1761 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-104977-778057", "unmarked_context_12_104977_778057", "Unmarked parent at depth 12, code 104977",
                "The frontier Boolean is false at remaining fuel 9, original node 778057, the whole prefixCache at depth 12 and code 104977, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-104989-779151", "unmarked_context_12_104989_779151", "Unmarked parent at depth 12, code 104989",
                "The frontier Boolean is false at remaining fuel 9, original node 779151, the whole prefixCache at depth 12 and code 104989, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-104977-778057", "node_context_12_104977_778057", "Original split at fuel 9 and node 778057",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 777957, 777996, 778027, 778056. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-104989-779151", "node_context_12_104989_779151", "Original split at fuel 9 and node 779151",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 779075, 779104, 779125, 779150. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-419910-778027", "context_13_419910_778027", "Context at depth 13, code 419910, node 778027",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 419910 and original node 778027, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-419961-779193", "context_13_419961_779193", "Context at depth 13, code 419961, node 779193",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 419961 and original node 779193, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
