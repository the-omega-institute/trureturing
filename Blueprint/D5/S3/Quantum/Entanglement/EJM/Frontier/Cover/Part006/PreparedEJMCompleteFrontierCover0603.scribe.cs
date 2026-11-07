using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0603Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0603.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0603",
        H("Original frontier context coverage 0603"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-28948", "selected_cut_28948", "Selected cut at depth 13, code 372847, node 731438",
                "At remaining fuel 8 and original index 731438, selection on the full partial prefix of depth 13 and code 372847 returns the complete row with depth 13, base-four code 372847, original node 731438, kind 2, reserved field 0, 945 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-28994", "selected_cut_28994", "Selected cut at depth 13, code 372896, node 732356",
                "At remaining fuel 8 and original index 732356, selection on the full partial prefix of depth 13 and code 372896 returns the complete row with depth 13, base-four code 372896, original node 732356, kind 2, reserved field 0, 621 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-93211-731439", "unmarked_context_12_93211_731439", "Unmarked parent at depth 12, code 93211",
                "The frontier Boolean is false at remaining fuel 9, original node 731439, the whole prefixCache at depth 12 and code 93211, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-23305-732346", "unmarked_context_11_23305_732346", "Unmarked parent at depth 11, code 23305",
                "The frontier Boolean is false at remaining fuel 10, original node 732346, the whole prefixCache at depth 11 and code 23305, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-93211-731439", "node_context_12_93211_731439", "Original split at fuel 9 and node 731439",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 731368, 731400, 731427, 731438. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-23305-732346", "node_context_11_23305_732346", "Original split at fuel 10 and node 732346",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 732093, 732170, 732258, 732345. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-372847-731438", "context_13_372847_731438", "Context at depth 13, code 372847, node 731438",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 372847 and original node 731438, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-372896-732356", "context_13_372896_732356", "Context at depth 13, code 372896, node 732356",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 372896 and original node 732356, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
