using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0251Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0251.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0251",
        H("Original frontier context coverage 0251"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-12050", "selected_cut_12050", "Selected cut at depth 12, code 25937, node 170504",
                "At remaining fuel 9 and original index 170504, selection on the full partial prefix of depth 12 and code 25937 returns the complete row with depth 12, base-four code 25937, original node 170504, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-12098", "selected_cut_12098", "Selected cut at depth 13, code 103844, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 103844 returns the complete row with depth 13, base-four code 103844, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-25938-320630", "unmarked_context_12_25938_320630", "Unmarked parent at depth 12, code 25938",
                "The frontier Boolean is false at remaining fuel 9, original node 320630, the whole prefixCache at depth 12 and code 25938, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-25960-321373", "unmarked_context_12_25960_321373", "Unmarked parent at depth 12, code 25960",
                "The frontier Boolean is false at remaining fuel 9, original node 321373, the whole prefixCache at depth 12 and code 25960, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-25938-320630", "node_context_12_25938_320630", "Original split at fuel 9 and node 320630",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 320596, 320621, 320629. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-25960-321373", "node_context_12_25960_321373", "Original split at fuel 9 and node 321373",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 321341, 321363, 321372. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-25937-170504", "context_12_25937_170504", "Context at depth 12, code 25937, node 170504",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25937 and original node 170504, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-103844-3444", "context_13_103844_3444", "Context at depth 13, code 103844, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 103844 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
