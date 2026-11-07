using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0188Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0188.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0188",
        H("Original frontier context coverage 0188"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-09027", "selected_cut_09027", "Selected cut at depth 13, code 93195, node 250286",
                "At remaining fuel 8 and original index 250286, selection on the full partial prefix of depth 13 and code 93195 returns the complete row with depth 13, base-four code 93195, original node 250286, kind 2, reserved field 0, 97 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-09074", "selected_cut_09074", "Selected cut at depth 14, code 372869, node 251481",
                "At remaining fuel 7 and original index 251481, selection on the full partial prefix of depth 14 and code 372869 returns the complete row with depth 14, base-four code 372869, original node 251481, kind 2, reserved field 0, 1153 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-23298-250287", "unmarked_context_12_23298_250287", "Unmarked parent at depth 12, code 23298",
                "The frontier Boolean is false at remaining fuel 9, original node 250287, the whole prefixCache at depth 12 and code 23298, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-5825-251387", "unmarked_context_11_5825_251387", "Unmarked parent at depth 11, code 5825",
                "The frontier Boolean is false at remaining fuel 10, original node 251387, the whole prefixCache at depth 11 and code 5825, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-23298-250287", "node_context_12_23298_250287", "Original split at fuel 9 and node 250287",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 250124, 250231, 250283, 250286. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-5825-251387", "node_context_11_5825_251387", "Original split at fuel 10 and node 251387",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 250739, 250921, 251186, 251386. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-93195-250286", "context_13_93195_250286", "Context at depth 13, code 93195, node 250286",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 93195 and original node 250286, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-14-372869-251481", "context_14_372869_251481", "Context at depth 14, code 372869, node 251481",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 372869 and original node 251481, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
