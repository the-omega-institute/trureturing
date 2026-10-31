using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0222Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0222.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0222",
        H("Original frontier context coverage 0222"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-10659", "selected_cut_10659", "Selected cut at depth 12, code 25164, node 288135",
                "At remaining fuel 9 and original index 288135, selection on the full partial prefix of depth 12 and code 25164 returns the complete row with depth 12, base-four code 25164, original node 288135, kind 2, reserved field 0, 3117 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-10706", "selected_cut_10706", "Selected cut at depth 12, code 25187, node 289062",
                "At remaining fuel 9 and original index 289062, selection on the full partial prefix of depth 12 and code 25187 returns the complete row with depth 12, base-four code 25187, original node 289062, kind 2, reserved field 0, 3805 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-6290-288096", "unmarked_context_11_6290_288096", "Unmarked parent at depth 11, code 6290",
                "The frontier Boolean is false at remaining fuel 10, original node 288096, the whole prefixCache at depth 11 and code 6290, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-25185-288991", "unmarked_context_12_25185_288991", "Unmarked parent at depth 12, code 25185",
                "The frontier Boolean is false at remaining fuel 9, original node 288991, the whole prefixCache at depth 12 and code 25185, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-6290-288096", "node_context_11_6290_288096", "Original split at fuel 10 and node 288096",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 287944, 287992, 288049, 288095. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-25185-288991", "node_context_12_25185_288991", "Original split at fuel 9 and node 288991",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 288951, 288979, 288990. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-6290-288096", "context_11_6290_288096", "Context at depth 11, code 6290, node 288096",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 6290 and original node 288096, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_25160_287944, context_12_25161_287992, context_12_25162_288049, context_12_25163_288095.", DescribeRole.Theorem),
            Node("context-12-25187-289062", "context_12_25187_289062", "Context at depth 12, code 25187, node 289062",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25187 and original node 289062, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
