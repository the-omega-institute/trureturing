using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0275Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0275.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0275",
        H("Original frontier context coverage 0275"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-13203", "selected_cut_13203", "Selected cut at depth 13, code 106527, node 348220",
                "At remaining fuel 8 and original index 348220, selection on the full partial prefix of depth 13 and code 106527 returns the complete row with depth 13, base-four code 106527, original node 348220, kind 2, reserved field 0, 1237 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-13250", "selected_cut_13250", "Selected cut at depth 13, code 106571, node 349573",
                "At remaining fuel 8 and original index 349573, selection on the full partial prefix of depth 13 and code 106571 returns the complete row with depth 13, base-four code 106571, original node 349573, kind 2, reserved field 0, 977 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26631-348221", "unmarked_context_12_26631_348221", "Unmarked parent at depth 12, code 26631",
                "The frontier Boolean is false at remaining fuel 9, original node 348221, the whole prefixCache at depth 12 and code 26631, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-26641-349501", "unmarked_context_12_26641_349501", "Unmarked parent at depth 12, code 26641",
                "The frontier Boolean is false at remaining fuel 9, original node 349501, the whole prefixCache at depth 12 and code 26641, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26631-348221", "node_context_12_26631_348221", "Original split at fuel 9 and node 348221",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 348102, 348179, 348203, 348220. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-26641-349501", "node_context_12_26641_349501", "Original split at fuel 9 and node 349501",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 349454, 349477, 349493, 349500. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-106527-348220", "context_13_106527_348220", "Context at depth 13, code 106527, node 348220",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 106527 and original node 348220, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-106571-349573", "context_13_106571_349573", "Context at depth 13, code 106571, node 349573",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 106571 and original node 349573, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
