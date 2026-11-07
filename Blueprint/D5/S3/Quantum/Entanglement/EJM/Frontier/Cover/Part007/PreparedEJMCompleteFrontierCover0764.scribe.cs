using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0764Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0764.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0764",
        H("Original frontier context coverage 0764"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-36676", "selected_cut_36676", "Selected cut at depth 12, code 289678, node 973842",
                "At remaining fuel 9 and original index 973842, selection on the full partial prefix of depth 12 and code 289678 returns the complete row with depth 12, base-four code 289678, original node 973842, kind 2, reserved field 0, 1565 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-36723", "selected_cut_36723", "Selected cut at depth 13, code 1162254, node 975271",
                "At remaining fuel 8 and original index 975271, selection on the full partial prefix of depth 13 and code 1162254 returns the complete row with depth 13, base-four code 1162254, original node 975271, kind 2, reserved field 0, 1117 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-72419-973843", "unmarked_context_11_72419_973843", "Unmarked parent at depth 11, code 72419",
                "The frontier Boolean is false at remaining fuel 10, original node 973843, the whole prefixCache at depth 11 and code 72419, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-290562-975165", "unmarked_context_12_290562_975165", "Unmarked parent at depth 12, code 290562",
                "The frontier Boolean is false at remaining fuel 9, original node 975165, the whole prefixCache at depth 12 and code 290562, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-72419-973843", "node_context_11_72419_973843", "Original split at fuel 10 and node 973843",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 973788, 973815, 973842, 903806. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-290562-975165", "node_context_12_290562_975165", "Original split at fuel 9 and node 975165",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 975083, 975112, 975140, 975164. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-289678-973842", "context_12_289678_973842", "Context at depth 12, code 289678, node 973842",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 289678 and original node 973842, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-1162254-975271", "context_13_1162254_975271", "Context at depth 13, code 1162254, node 975271",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1162254 and original node 975271, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
