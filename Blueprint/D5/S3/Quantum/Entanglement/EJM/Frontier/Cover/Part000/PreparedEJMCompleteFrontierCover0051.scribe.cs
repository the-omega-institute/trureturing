using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0051Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0051.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0051",
        H("Original frontier context coverage 0051"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-02451", "selected_cut_02451", "Selected cut at depth 13, code 22770, node 79303",
                "At remaining fuel 8 and original index 79303, selection on the full partial prefix of depth 13 and code 22770 returns the complete row with depth 13, base-four code 22770, original node 79303, kind 2, reserved field 0, 2637 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-02497", "selected_cut_02497", "Selected cut at depth 13, code 22816, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 22816 returns the complete row with depth 13, base-four code 22816, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-5692-79320", "unmarked_context_12_5692_79320", "Unmarked parent at depth 12, code 5692",
                "The frontier Boolean is false at remaining fuel 9, original node 79320, the whole prefixCache at depth 12 and code 5692, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-1425-80046", "unmarked_context_11_1425_80046", "Unmarked parent at depth 11, code 1425",
                "The frontier Boolean is false at remaining fuel 10, original node 80046, the whole prefixCache at depth 11 and code 1425, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-5692-79320", "node_context_12_5692_79320", "Original split at fuel 9 and node 79320",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 79211, 79259, 79303, 79319. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-1425-80046", "node_context_11_1425_80046", "Original split at fuel 10 and node 80046",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 79856, 79912, 79971, 80045. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-22770-79303", "context_13_22770_79303", "Context at depth 13, code 22770, node 79303",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 22770 and original node 79303, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-22816-3444", "context_13_22816_3444", "Context at depth 13, code 22816, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 22816 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
