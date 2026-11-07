using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0673Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0673.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0673",
        H("Original frontier context coverage 0673"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-32307", "selected_cut_32307", "Selected cut at depth 11, code 27075, node 815335",
                "At remaining fuel 10 and original index 815335, selection on the full partial prefix of depth 11 and code 27075 returns the complete row with depth 11, base-four code 27075, original node 815335, kind 2, reserved field 0, 5 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-32354", "selected_cut_32354", "Selected cut at depth 13, code 433280, node 831640",
                "At remaining fuel 8 and original index 831640, selection on the full partial prefix of depth 13 and code 433280 returns the complete row with depth 13, base-four code 433280, original node 831640, kind 2, reserved field 0, 1425 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-6768-830451", "unmarked_context_10_6768_830451", "Unmarked parent at depth 10, code 6768",
                "The frontier Boolean is false at remaining fuel 11, original node 830451, the whole prefixCache at depth 10 and code 6768, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-6769-831609", "unmarked_context_10_6769_831609", "Unmarked parent at depth 10, code 6769",
                "The frontier Boolean is false at remaining fuel 11, original node 831609, the whole prefixCache at depth 10 and code 6769, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-6768-830451", "node_context_10_6768_830451", "Original split at fuel 11 and node 830451",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 434745, 167448, 830450, 815335. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-6769-831609", "node_context_10_6769_831609", "Original split at fuel 11 and node 831609",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 830902, 815620, 831311, 831608. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-27075-815335", "context_11_27075_815335", "Context at depth 11, code 27075, node 815335",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 27075 and original node 815335, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-433280-831640", "context_13_433280_831640", "Context at depth 13, code 433280, node 831640",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 433280 and original node 831640, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
