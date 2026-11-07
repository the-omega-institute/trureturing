using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0670Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0670.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0670",
        H("Original frontier context coverage 0670"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-32163", "selected_cut_32163", "Selected cut at depth 12, code 107847, node 826013",
                "At remaining fuel 9 and original index 826013, selection on the full partial prefix of depth 12 and code 107847 returns the complete row with depth 12, base-four code 107847, original node 826013, kind 2, reserved field 0, 3837 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-32210", "selected_cut_32210", "Selected cut at depth 12, code 107876, node 827378",
                "At remaining fuel 9 and original index 827378, selection on the full partial prefix of depth 12 and code 107876 returns the complete row with depth 12, base-four code 107876, original node 827378, kind 2, reserved field 0, 3325 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-26961-826014", "unmarked_context_11_26961_826014", "Unmarked parent at depth 11, code 26961",
                "The frontier Boolean is false at remaining fuel 10, original node 826014, the whole prefixCache at depth 11 and code 26961, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-26968-827324", "unmarked_context_11_26968_827324", "Unmarked parent at depth 11, code 26968",
                "The frontier Boolean is false at remaining fuel 10, original node 827324, the whole prefixCache at depth 11 and code 26968, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-26961-826014", "node_context_11_26961_826014", "Original split at fuel 10 and node 826014",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 825888, 692443, 825934, 826013. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-26968-827324", "node_context_11_26968_827324", "Original split at fuel 10 and node 827324",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 827148, 827193, 827251, 827323. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-107847-826013", "context_12_107847_826013", "Context at depth 12, code 107847, node 826013",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 107847 and original node 826013, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-107876-827378", "context_12_107876_827378", "Context at depth 12, code 107876, node 827378",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 107876 and original node 827378, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
