using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0593Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0593.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0593",
        H("Original frontier context coverage 0593"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-28468", "selected_cut_28468", "Selected cut at depth 13, code 369847, node 718709",
                "At remaining fuel 8 and original index 718709, selection on the full partial prefix of depth 13 and code 369847 returns the complete row with depth 13, base-four code 369847, original node 718709, kind 2, reserved field 0, 817 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-28515", "selected_cut_28515", "Selected cut at depth 13, code 369897, node 719391",
                "At remaining fuel 8 and original index 719391, selection on the full partial prefix of depth 13 and code 369897 returns the complete row with depth 13, base-four code 369897, original node 719391, kind 2, reserved field 0, 1613 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-92461-718710", "unmarked_context_12_92461_718710", "Unmarked parent at depth 12, code 92461",
                "The frontier Boolean is false at remaining fuel 9, original node 718710, the whole prefixCache at depth 12 and code 92461, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-92473-719364", "unmarked_context_12_92473_719364", "Unmarked parent at depth 12, code 92473",
                "The frontier Boolean is false at remaining fuel 9, original node 719364, the whole prefixCache at depth 12 and code 92473, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-92461-718710", "node_context_12_92461_718710", "Original split at fuel 9 and node 718710",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 718666, 718685, 718703, 718709. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-92473-719364", "node_context_12_92473_719364", "Original split at fuel 9 and node 719364",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 719316, 719338, 719355, 719363. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-369847-718709", "context_13_369847_718709", "Context at depth 13, code 369847, node 718709",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 369847 and original node 718709, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-369897-719391", "context_13_369897_719391", "Context at depth 13, code 369897, node 719391",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 369897 and original node 719391, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
