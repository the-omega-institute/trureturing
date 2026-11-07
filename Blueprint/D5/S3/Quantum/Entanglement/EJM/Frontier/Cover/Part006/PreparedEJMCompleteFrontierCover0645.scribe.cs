using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0645Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0645.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0645",
        H("Original frontier context coverage 0645"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-30964", "selected_cut_30964", "Selected cut at depth 12, code 105337, node 788006",
                "At remaining fuel 9 and original index 788006, selection on the full partial prefix of depth 12 and code 105337 returns the complete row with depth 12, base-four code 105337, original node 788006, kind 2, reserved field 0, 1349 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-31010", "selected_cut_31010", "Selected cut at depth 13, code 421970, node 789794",
                "At remaining fuel 8 and original index 789794, selection on the full partial prefix of depth 13 and code 421970 returns the complete row with depth 13, base-four code 421970, original node 789794, kind 2, reserved field 0, 1457 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-26334-788063", "unmarked_context_11_26334_788063", "Unmarked parent at depth 11, code 26334",
                "The frontier Boolean is false at remaining fuel 10, original node 788063, the whole prefixCache at depth 11 and code 26334, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-26372-789695", "unmarked_context_11_26372_789695", "Unmarked parent at depth 11, code 26372",
                "The frontier Boolean is false at remaining fuel 10, original node 789695, the whole prefixCache at depth 11 and code 26372, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-26334-788063", "node_context_11_26334_788063", "Original split at fuel 10 and node 788063",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 787978, 788006, 788036, 788062. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-26372-789695", "node_context_11_26372_789695", "Original split at fuel 10 and node 789695",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 789343, 789483, 789585, 789694. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-105337-788006", "context_12_105337_788006", "Context at depth 12, code 105337, node 788006",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 105337 and original node 788006, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-421970-789794", "context_13_421970_789794", "Context at depth 13, code 421970, node 789794",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 421970 and original node 789794, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
