using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0140Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0140.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0140",
        H("Original frontier context coverage 0140"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-06723", "selected_cut_06723", "Selected cut at depth 13, code 87387, node 199234",
                "At remaining fuel 8 and original index 199234, selection on the full partial prefix of depth 13 and code 87387 returns the complete row with depth 13, base-four code 87387, original node 199234, kind 2, reserved field 0, 977 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-06770", "selected_cut_06770", "Selected cut at depth 12, code 21899, node 200596",
                "At remaining fuel 9 and original index 200596, selection on the full partial prefix of depth 12 and code 21899 returns the complete row with depth 12, base-four code 21899, original node 200596, kind 2, reserved field 0, 2333 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-21846-199235", "unmarked_context_12_21846_199235", "Unmarked parent at depth 12, code 21846",
                "The frontier Boolean is false at remaining fuel 9, original node 199235, the whole prefixCache at depth 12 and code 21846, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-5473-200439", "unmarked_context_11_5473_200439", "Unmarked parent at depth 11, code 5473",
                "The frontier Boolean is false at remaining fuel 10, original node 200439, the whole prefixCache at depth 11 and code 5473, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-21846-199235", "node_context_12_21846_199235", "Original split at fuel 9 and node 199235",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 199205, 199225, 199234. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-5473-200439", "node_context_11_5473_200439", "Original split at fuel 10 and node 200439",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 200318, 200363, 200401, 200438. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-87387-199234", "context_13_87387_199234", "Context at depth 13, code 87387, node 199234",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 87387 and original node 199234, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-21899-200596", "context_12_21899_200596", "Context at depth 12, code 21899, node 200596",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 21899 and original node 200596, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
