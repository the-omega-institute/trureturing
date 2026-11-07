using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0649Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0649.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0649",
        H("Original frontier context coverage 0649"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-31155", "selected_cut_31155", "Selected cut at depth 13, code 422274, node 794213",
                "At remaining fuel 8 and original index 794213, selection on the full partial prefix of depth 13 and code 422274 returns the complete row with depth 13, base-four code 422274, original node 794213, kind 2, reserved field 0, 1489 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-31202", "selected_cut_31202", "Selected cut at depth 12, code 105734, node 763842",
                "At remaining fuel 9 and original index 763842, selection on the full partial prefix of depth 12 and code 105734 returns the complete row with depth 12, base-four code 105734, original node 763842, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-105568-794239", "unmarked_context_12_105568_794239", "Unmarked parent at depth 12, code 105568",
                "The frontier Boolean is false at remaining fuel 9, original node 794239, the whole prefixCache at depth 12 and code 105568, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-105733-796455", "unmarked_context_12_105733_796455", "Unmarked parent at depth 12, code 105733",
                "The frontier Boolean is false at remaining fuel 9, original node 796455, the whole prefixCache at depth 12 and code 105733, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-105568-794239", "node_context_12_105568_794239", "Original split at fuel 9 and node 794239",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 794131, 794213, 794238. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-105733-796455", "node_context_12_105733_796455", "Original split at fuel 9 and node 796455",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 796225, 796423, 796448, 796454. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-422274-794213", "context_13_422274_794213", "Context at depth 13, code 422274, node 794213",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 422274 and original node 794213, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-105734-763842", "context_12_105734_763842", "Context at depth 12, code 105734, node 763842",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 105734 and original node 763842, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
