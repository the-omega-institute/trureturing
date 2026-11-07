using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0695Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0695.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0695",
        H("Original frontier context coverage 0695"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-33363", "selected_cut_33363", "Selected cut at depth 13, code 440640, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 440640 returns the complete row with depth 13, base-four code 440640, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-33411", "selected_cut_33411", "Selected cut at depth 12, code 110193, node 860061",
                "At remaining fuel 9 and original index 860061, selection on the full partial prefix of depth 12 and code 110193 returns the complete row with depth 12, base-four code 110193, original node 860061, kind 2, reserved field 0, 2553 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-110160-858498", "unmarked_context_12_110160_858498", "Unmarked parent at depth 12, code 110160",
                "The frontier Boolean is false at remaining fuel 9, original node 858498, the whole prefixCache at depth 12 and code 110160, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-6886-859974", "unmarked_context_10_6886_859974", "Unmarked parent at depth 10, code 6886",
                "The frontier Boolean is false at remaining fuel 11, original node 859974, the whole prefixCache at depth 10 and code 6886, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-110160-858498", "node_context_12_110160_858498", "Original split at fuel 9 and node 858498",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 858454, 858489, 858497. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-6886-859974", "node_context_10_6886_859974", "Original split at fuel 11 and node 859974",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 859519, 859716, 859822, 859973. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-440640-3444", "context_13_440640_3444", "Context at depth 13, code 440640, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 440640 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-110193-860061", "context_12_110193_860061", "Context at depth 12, code 110193, node 860061",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 110193 and original node 860061, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
