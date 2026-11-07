using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0957Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0957.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0957",
        H("Original frontier context coverage 0957"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-45939", "selected_cut_45939", "Selected cut at depth 12, code 369441, node 1278003",
                "At remaining fuel 9 and original index 1278003, selection on the full partial prefix of depth 12 and code 369441 returns the complete row with depth 12, base-four code 369441, original node 1278003, kind 2, reserved field 0, 3077 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-45986", "selected_cut_45986", "Selected cut at depth 10, code 23093, node 893098",
                "At remaining fuel 11 and original index 893098, selection on the full partial prefix of depth 10 and code 23093 returns the complete row with depth 10, base-four code 23093, original node 893098, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-92360-1278091", "unmarked_context_11_92360_1278091", "Unmarked parent at depth 11, code 92360",
                "The frontier Boolean is false at remaining fuel 10, original node 1278091, the whole prefixCache at depth 11 and code 92360, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-23092-1279745", "unmarked_context_10_23092_1279745", "Unmarked parent at depth 10, code 23092",
                "The frontier Boolean is false at remaining fuel 11, original node 1279745, the whole prefixCache at depth 10 and code 23092, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-92360-1278091", "node_context_11_92360_1278091", "Original split at fuel 10 and node 1278091",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435790, 1278003, 1278045, 1278090. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-23092-1279745", "node_context_10_23092_1279745", "Original split at fuel 11 and node 1279745",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 907917, 1279533, 1279661, 1279744. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-369441-1278003", "context_12_369441_1278003", "Context at depth 12, code 369441, node 1278003",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 369441 and original node 1278003, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-23093-893098", "context_10_23093_893098", "Context at depth 10, code 23093, node 893098",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 23093 and original node 893098, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
