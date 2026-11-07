using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0235Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0235.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0235",
        H("Original frontier context coverage 0235"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-11282", "selected_cut_11282", "Selected cut at depth 13, code 102434, node 302638",
                "At remaining fuel 8 and original index 302638, selection on the full partial prefix of depth 13 and code 102434 returns the complete row with depth 13, base-four code 102434, original node 302638, kind 2, reserved field 0, 2313 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-11330", "selected_cut_11330", "Selected cut at depth 13, code 102479, node 304033",
                "At remaining fuel 8 and original index 304033, selection on the full partial prefix of depth 13 and code 102479 returns the complete row with depth 13, base-four code 102479, original node 304033, kind 2, reserved field 0, 777 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-25608-302652", "unmarked_context_12_25608_302652", "Unmarked parent at depth 12, code 25608",
                "The frontier Boolean is false at remaining fuel 9, original node 302652, the whole prefixCache at depth 12 and code 25608, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-25618-303956", "unmarked_context_12_25618_303956", "Unmarked parent at depth 12, code 25618",
                "The frontier Boolean is false at remaining fuel 9, original node 303956, the whole prefixCache at depth 12 and code 25618, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-25608-302652", "node_context_12_25608_302652", "Original split at fuel 9 and node 302652",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 302537, 302610, 302638, 302651. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-25618-303956", "node_context_12_25618_303956", "Original split at fuel 9 and node 303956",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 303895, 303923, 303941, 303955. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-102434-302638", "context_13_102434_302638", "Context at depth 13, code 102434, node 302638",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 102434 and original node 302638, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-102479-304033", "context_13_102479_304033", "Context at depth 13, code 102479, node 304033",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 102479 and original node 304033, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
