using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0143Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0143.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0143",
        H("Original frontier context coverage 0143"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-06866", "selected_cut_06866", "Selected cut at depth 13, code 88112, node 203301",
                "At remaining fuel 8 and original index 203301, selection on the full partial prefix of depth 13 and code 88112 returns the complete row with depth 13, base-four code 88112, original node 203301, kind 2, reserved field 0, 2073 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-06914", "selected_cut_06914", "Selected cut at depth 13, code 88154, node 204448",
                "At remaining fuel 8 and original index 204448, selection on the full partial prefix of depth 13 and code 88154 returns the complete row with depth 13, base-four code 88154, original node 204448, kind 2, reserved field 0, 1641 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-22028-203407", "unmarked_context_12_22028_203407", "Unmarked parent at depth 12, code 22028",
                "The frontier Boolean is false at remaining fuel 9, original node 203407, the whole prefixCache at depth 12 and code 22028, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-22037-204357", "unmarked_context_12_22037_204357", "Unmarked parent at depth 12, code 22037",
                "The frontier Boolean is false at remaining fuel 9, original node 204357, the whole prefixCache at depth 12 and code 22037, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-22028-203407", "node_context_12_22028_203407", "Original split at fuel 9 and node 203407",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 203301, 203357, 203387, 203406. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-22037-204357", "node_context_12_22037_204357", "Original split at fuel 9 and node 204357",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 204276, 204325, 204349, 204356. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-88112-203301", "context_13_88112_203301", "Context at depth 13, code 88112, node 203301",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 88112 and original node 203301, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-88154-204448", "context_13_88154_204448", "Context at depth 13, code 88154, node 204448",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 88154 and original node 204448, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
