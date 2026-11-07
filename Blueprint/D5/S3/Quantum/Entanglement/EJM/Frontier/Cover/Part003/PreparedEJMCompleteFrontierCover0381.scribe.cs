using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0381Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0381.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0381",
        H("Original frontier context coverage 0381"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-18291", "selected_cut_18291", "Selected cut at depth 12, code 71274, node 445248",
                "At remaining fuel 9 and original index 445248, selection on the full partial prefix of depth 12 and code 71274 returns the complete row with depth 12, base-four code 71274, original node 445248, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-18338", "selected_cut_18338", "Selected cut at depth 12, code 71318, node 469617",
                "At remaining fuel 9 and original index 469617, selection on the full partial prefix of depth 12 and code 71318 returns the complete row with depth 12, base-four code 71318, original node 469617, kind 2, reserved field 0, 2357 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-17818-468346", "unmarked_context_11_17818_468346", "Unmarked parent at depth 11, code 17818",
                "The frontier Boolean is false at remaining fuel 10, original node 468346, the whole prefixCache at depth 11 and code 17818, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-17828-469564", "unmarked_context_11_17828_469564", "Unmarked parent at depth 11, code 17828",
                "The frontier Boolean is false at remaining fuel 10, original node 469564, the whole prefixCache at depth 11 and code 17828, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-17818-468346", "node_context_11_17818_468346", "Original split at fuel 10 and node 468346",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 468252, 468298, 445248, 468345. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-17828-469564", "node_context_11_17828_469564", "Original split at fuel 10 and node 469564",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 469507, 469526, 469541, 469563. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-71274-445248", "context_12_71274_445248", "Context at depth 12, code 71274, node 445248",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 71274 and original node 445248, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-71318-469617", "context_12_71318_469617", "Context at depth 12, code 71318, node 469617",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 71318 and original node 469617, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
