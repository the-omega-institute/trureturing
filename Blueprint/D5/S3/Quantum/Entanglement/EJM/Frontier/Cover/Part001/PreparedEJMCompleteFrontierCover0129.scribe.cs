using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0129Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0129.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0129",
        H("Original frontier context coverage 0129"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-06195", "selected_cut_06195", "Selected cut at depth 12, code 21102, node 186445",
                "At remaining fuel 9 and original index 186445, selection on the full partial prefix of depth 12 and code 21102 returns the complete row with depth 12, base-four code 21102, original node 186445, kind 2, reserved field 0, 3777 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-06242", "selected_cut_06242", "Selected cut at depth 12, code 21146, node 187877",
                "At remaining fuel 9 and original index 187877, selection on the full partial prefix of depth 12 and code 21146 returns the complete row with depth 12, base-four code 21146, original node 187877, kind 2, reserved field 0, 3265 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-5275-186484", "unmarked_context_11_5275_186484", "Unmarked parent at depth 11, code 5275",
                "The frontier Boolean is false at remaining fuel 10, original node 186484, the whole prefixCache at depth 11 and code 5275, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-5285-187786", "unmarked_context_11_5285_187786", "Unmarked parent at depth 11, code 5285",
                "The frontier Boolean is false at remaining fuel 10, original node 187786, the whole prefixCache at depth 11 and code 5285, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-5275-186484", "node_context_11_5275_186484", "Original split at fuel 10 and node 186484",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 186342, 186404, 186445, 186483. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-5285-187786", "node_context_11_5285_187786", "Original split at fuel 10 and node 187786",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 187713, 187736, 187759, 187785. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-21102-186445", "context_12_21102_186445", "Context at depth 12, code 21102, node 186445",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 21102 and original node 186445, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-21146-187877", "context_12_21146_187877", "Context at depth 12, code 21146, node 187877",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 21146 and original node 187877, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
