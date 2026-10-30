using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0463Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0463.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0463",
        H("Original frontier context coverage 0463"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-22227", "selected_cut_22227", "Selected cut at depth 13, code 302232, node 566464",
                "At remaining fuel 8 and original index 566464, selection on the full partial prefix of depth 13 and code 302232 returns the complete row with depth 13, base-four code 302232, original node 566464, kind 2, reserved field 0, 1185 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-22275", "selected_cut_22275", "Selected cut at depth 13, code 302286, node 567378",
                "At remaining fuel 8 and original index 567378, selection on the full partial prefix of depth 13 and code 302286 returns the complete row with depth 13, base-four code 302286, original node 567378, kind 2, reserved field 0, 1629 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-75558-566521", "unmarked_context_12_75558_566521", "Unmarked parent at depth 12, code 75558",
                "The frontier Boolean is false at remaining fuel 9, original node 566521, the whole prefixCache at depth 12 and code 75558, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-75570-567328", "unmarked_context_12_75570_567328", "Unmarked parent at depth 12, code 75570",
                "The frontier Boolean is false at remaining fuel 9, original node 567328, the whole prefixCache at depth 12 and code 75570, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-75558-566521", "node_context_12_75558_566521", "Original split at fuel 9 and node 566521",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 566464, 566492, 566511, 566520. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-75570-567328", "node_context_12_75570_567328", "Original split at fuel 9 and node 567328",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 567268, 567302, 567321, 567327. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-302232-566464", "context_13_302232_566464", "Context at depth 13, code 302232, node 566464",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 302232 and original node 566464, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-302286-567378", "context_13_302286_567378", "Context at depth 13, code 302286, node 567378",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 302286 and original node 567378, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
