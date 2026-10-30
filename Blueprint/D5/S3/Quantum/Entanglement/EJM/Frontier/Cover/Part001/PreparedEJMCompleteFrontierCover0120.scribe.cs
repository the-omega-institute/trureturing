using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0120Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0120.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0120",
        H("Original frontier context coverage 0120"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-05762", "selected_cut_05762", "Selected cut at depth 11, code 5207, node 1736",
                "At remaining fuel 10 and original index 1736, selection on the full partial prefix of depth 11 and code 5207 returns the complete row with depth 11, base-four code 5207, original node 1736, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-05809", "selected_cut_05809", "Selected cut at depth 12, code 20887, node 177754",
                "At remaining fuel 9 and original index 177754, selection on the full partial prefix of depth 12 and code 20887 returns the complete row with depth 12, base-four code 20887, original node 177754, kind 2, reserved field 0, 1177 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-1301-176438", "unmarked_context_10_1301_176438", "Unmarked parent at depth 10, code 1301",
                "The frontier Boolean is false at remaining fuel 11, original node 176438, the whole prefixCache at depth 10 and code 1301, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-5221-177755", "unmarked_context_11_5221_177755", "Unmarked parent at depth 11, code 5221",
                "The frontier Boolean is false at remaining fuel 10, original node 177755, the whole prefixCache at depth 11 and code 5221, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-1301-176438", "node_context_10_1301_176438", "Original split at fuel 11 and node 176438",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 176160, 176226, 176437, 1736. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-5221-177755", "node_context_11_5221_177755", "Original split at fuel 10 and node 177755",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 177691, 177716, 177735, 177754. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-5207-1736", "context_11_5207_1736", "Context at depth 11, code 5207, node 1736",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 5207 and original node 1736, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-5221-177755", "context_11_5221_177755", "Context at depth 11, code 5221, node 177755",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 5221 and original node 177755, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_20884_177691, context_12_20885_177716, context_12_20886_177735, context_12_20887_177754.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
