using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0954Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0954.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0954",
        H("Original frontier context coverage 0954"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-45795", "selected_cut_45795", "Selected cut at depth 11, code 92256, node 907917",
                "At remaining fuel 10 and original index 907917, selection on the full partial prefix of depth 11 and code 92256 returns the complete row with depth 11, base-four code 92256, original node 907917, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-45842", "selected_cut_45842", "Selected cut at depth 12, code 369188, node 1274531",
                "At remaining fuel 9 and original index 1274531, selection on the full partial prefix of depth 12 and code 369188 returns the complete row with depth 12, base-four code 369188, original node 1274531, kind 2, reserved field 0, 3801 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-5765-1272954", "unmarked_context_9_5765_1272954", "Unmarked parent at depth 9, code 5765",
                "The frontier Boolean is false at remaining fuel 12, original node 1272954, the whole prefixCache at depth 9 and code 5765, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-92296-1274447", "unmarked_context_11_92296_1274447", "Unmarked parent at depth 11, code 92296",
                "The frontier Boolean is false at remaining fuel 10, original node 1274447, the whole prefixCache at depth 11 and code 92296, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-5765-1272954", "node_context_9_5765_1272954", "Original split at fuel 12 and node 1272954",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1272445, 893098, 1272723, 1272953. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-92296-1274447", "node_context_11_92296_1274447", "Original split at fuel 10 and node 1274447",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435790, 1274372, 1274407, 1274446. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-9-5765-1272954", "context_9_5765_1272954", "Context at depth 9, code 5765, node 1272954",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 5765 and original node 1272954, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_23060_1272445, context_10_23061_893098, context_10_23062_1272723, context_10_23063_1272953.", DescribeRole.Theorem),
            Node("context-12-369188-1274531", "context_12_369188_1274531", "Context at depth 12, code 369188, node 1274531",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 369188 and original node 1274531, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
