using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0650Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0650.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0650",
        H("Original frontier context coverage 0650"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-31203", "selected_cut_31203", "Selected cut at depth 14, code 1691760, node 796483",
                "At remaining fuel 7 and original index 796483, selection on the full partial prefix of depth 14 and code 1691760 returns the complete row with depth 14, base-four code 1691760, original node 796483, kind 2, reserved field 0, 577 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-31251", "selected_cut_31251", "Selected cut at depth 13, code 423006, node 798785",
                "At remaining fuel 8 and original index 798785, selection on the full partial prefix of depth 13 and code 423006 returns the complete row with depth 13, base-four code 423006, original node 798785, kind 2, reserved field 0, 2173 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-422940-796625", "unmarked_context_13_422940_796625", "Unmarked parent at depth 13, code 422940",
                "The frontier Boolean is false at remaining fuel 8, original node 796625, the whole prefixCache at depth 13 and code 422940, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-105750-798586", "unmarked_context_12_105750_798586", "Unmarked parent at depth 12, code 105750",
                "The frontier Boolean is false at remaining fuel 9, original node 798586, the whole prefixCache at depth 12 and code 105750, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-422940-796625", "node_context_13_422940_796625", "Original split at fuel 8 and node 796625",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 796483, 796523, 796592, 796624. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-105750-798586", "node_context_12_105750_798586", "Original split at fuel 9 and node 798586",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 798500, 798538, 798572, 798585. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-14-1691760-796483", "context_14_1691760_796483", "Context at depth 14, code 1691760, node 796483",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 1691760 and original node 796483, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-423006-798785", "context_13_423006_798785", "Context at depth 13, code 423006, node 798785",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 423006 and original node 798785, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
