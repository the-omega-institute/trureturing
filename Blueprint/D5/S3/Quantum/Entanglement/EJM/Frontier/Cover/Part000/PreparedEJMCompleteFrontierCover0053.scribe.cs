using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0053Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0053.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0053",
        H("Original frontier context coverage 0053"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-02547", "selected_cut_02547", "Selected cut at depth 13, code 22863, node 80905",
                "At remaining fuel 8 and original index 80905, selection on the full partial prefix of depth 13 and code 22863 returns the complete row with depth 13, base-four code 22863, original node 80905, kind 2, reserved field 0, 1037 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-02595", "selected_cut_02595", "Selected cut at depth 13, code 22911, node 82051",
                "At remaining fuel 8 and original index 82051, selection on the full partial prefix of depth 13 and code 22911 returns the complete row with depth 13, base-four code 22911, original node 82051, kind 2, reserved field 0, 1169 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-5715-80906", "unmarked_context_12_5715_80906", "Unmarked parent at depth 12, code 5715",
                "The frontier Boolean is false at remaining fuel 9, original node 80906, the whole prefixCache at depth 12 and code 5715, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-5726-81996", "unmarked_context_12_5726_81996", "Unmarked parent at depth 12, code 5726",
                "The frontier Boolean is false at remaining fuel 9, original node 81996, the whole prefixCache at depth 12 and code 5726, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-5715-80906", "node_context_12_5715_80906", "Original split at fuel 9 and node 80906",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 80870, 80892, 80905. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-5726-81996", "node_context_12_5726_81996", "Original split at fuel 9 and node 81996",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 81953, 81977, 81995. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-22863-80905", "context_13_22863_80905", "Context at depth 13, code 22863, node 80905",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 22863 and original node 80905, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-22911-82051", "context_13_22911_82051", "Context at depth 13, code 22911, node 82051",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 22911 and original node 82051, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
