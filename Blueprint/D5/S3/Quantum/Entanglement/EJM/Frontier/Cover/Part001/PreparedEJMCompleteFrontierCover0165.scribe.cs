using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0165Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0165.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0165",
        H("Original frontier context coverage 0165"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-07923", "selected_cut_07923", "Selected cut at depth 13, code 91167, node 226366",
                "At remaining fuel 8 and original index 226366, selection on the full partial prefix of depth 13 and code 91167 returns the complete row with depth 13, base-four code 91167, original node 226366, kind 2, reserved field 0, 1217 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-07970", "selected_cut_07970", "Selected cut at depth 13, code 91199, node 227426",
                "At remaining fuel 8 and original index 227426, selection on the full partial prefix of depth 13 and code 91199 returns the complete row with depth 13, base-four code 91199, original node 227426, kind 2, reserved field 0, 1281 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-22791-226367", "unmarked_context_12_22791_226367", "Unmarked parent at depth 12, code 22791",
                "The frontier Boolean is false at remaining fuel 9, original node 226367, the whole prefixCache at depth 12 and code 22791, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-22799-227427", "unmarked_context_12_22799_227427", "Unmarked parent at depth 12, code 22799",
                "The frontier Boolean is false at remaining fuel 9, original node 227427, the whole prefixCache at depth 12 and code 22799, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-22791-226367", "node_context_12_22791_226367", "Original split at fuel 9 and node 226367",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 226274, 226338, 226357, 226366. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-22799-227427", "node_context_12_22799_227427", "Original split at fuel 9 and node 227427",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 227344, 227404, 227418, 227426. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-91167-226366", "context_13_91167_226366", "Context at depth 13, code 91167, node 226366",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 91167 and original node 226366, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-22799-227427", "context_12_22799_227427", "Context at depth 12, code 22799, node 227427",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 22799 and original node 227427, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_91196_227344, context_13_91197_227404, context_13_91198_227418, context_13_91199_227426.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
