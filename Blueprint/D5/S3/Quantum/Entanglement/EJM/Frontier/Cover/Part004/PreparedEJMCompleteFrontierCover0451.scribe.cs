using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0451Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0451.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0451",
        H("Original frontier context coverage 0451"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-21651", "selected_cut_21651", "Selected cut at depth 12, code 75147, node 554006",
                "At remaining fuel 9 and original index 554006, selection on the full partial prefix of depth 12 and code 75147 returns the complete row with depth 12, base-four code 75147, original node 554006, kind 2, reserved field 0, 2785 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-21699", "selected_cut_21699", "Selected cut at depth 12, code 75198, node 555062",
                "At remaining fuel 9 and original index 555062, selection on the full partial prefix of depth 12 and code 75198 returns the complete row with depth 12, base-four code 75198, original node 555062, kind 2, reserved field 0, 1181 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-18786-554007", "unmarked_context_11_18786_554007", "Unmarked parent at depth 11, code 18786",
                "The frontier Boolean is false at remaining fuel 10, original node 554007, the whole prefixCache at depth 11 and code 18786, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-18798-555028", "unmarked_context_11_18798_555028", "Unmarked parent at depth 11, code 18798",
                "The frontier Boolean is false at remaining fuel 10, original node 555028, the whole prefixCache at depth 11 and code 18798, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-18786-554007", "node_context_11_18786_554007", "Original split at fuel 10 and node 554007",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 553865, 553909, 553952, 554006. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-18798-555028", "node_context_11_18798_555028", "Original split at fuel 10 and node 555028",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 554971, 554986, 555006, 555027. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-75147-554006", "context_12_75147_554006", "Context at depth 12, code 75147, node 554006",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 75147 and original node 554006, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-75198-555062", "context_12_75198_555062", "Context at depth 12, code 75198, node 555062",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 75198 and original node 555062, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
