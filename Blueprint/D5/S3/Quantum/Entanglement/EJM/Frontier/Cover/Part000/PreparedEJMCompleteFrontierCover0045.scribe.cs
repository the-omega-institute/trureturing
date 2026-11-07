using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0045Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0045.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0045",
        H("Original frontier context coverage 0045"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-02162", "selected_cut_02162", "Selected cut at depth 13, code 22547, node 71447",
                "At remaining fuel 8 and original index 71447, selection on the full partial prefix of depth 13 and code 22547 returns the complete row with depth 13, base-four code 22547, original node 71447, kind 2, reserved field 0, 1753 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-02210", "selected_cut_02210", "Selected cut at depth 13, code 22571, node 72949",
                "At remaining fuel 8 and original index 72949, selection on the full partial prefix of depth 13 and code 22571 returns the complete row with depth 13, base-four code 22571, original node 72949, kind 2, reserved field 0, 2093 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-5636-71448", "unmarked_context_12_5636_71448", "Unmarked parent at depth 12, code 5636",
                "The frontier Boolean is false at remaining fuel 9, original node 71448, the whole prefixCache at depth 12 and code 5636, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-13-22569-72816", "unmarked_context_13_22569_72816", "Unmarked parent at depth 13, code 22569",
                "The frontier Boolean is false at remaining fuel 8, original node 72816, the whole prefixCache at depth 13 and code 22569, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-5636-71448", "node_context_12_5636_71448", "Original split at fuel 9 and node 71448",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 71231, 71332, 71400, 71447. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-13-22569-72816", "node_context_13_22569_72816", "Original split at fuel 8 and node 72816",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 72719, 72748, 72786, 72815. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-22547-71447", "context_13_22547_71447", "Context at depth 13, code 22547, node 71447",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 22547 and original node 71447, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-22571-72949", "context_13_22571_72949", "Context at depth 13, code 22571, node 72949",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 22571 and original node 72949, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
