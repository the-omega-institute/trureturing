using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0896Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0896.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0896",
        H("Original frontier context coverage 0896"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-43011", "selected_cut_43011", "Selected cut at depth 12, code 339219, node 1176055",
                "At remaining fuel 9 and original index 1176055, selection on the full partial prefix of depth 12 and code 339219 returns the complete row with depth 12, base-four code 339219, original node 1176055, kind 2, reserved field 0, 2929 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-43058", "selected_cut_43058", "Selected cut at depth 12, code 339272, node 1177247",
                "At remaining fuel 9 and original index 1177247, selection on the full partial prefix of depth 12 and code 339272 returns the complete row with depth 12, base-four code 339272, original node 1177247, kind 2, reserved field 0, 1589 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84804-1176056", "unmarked_context_11_84804_1176056", "Unmarked parent at depth 11, code 84804",
                "The frontier Boolean is false at remaining fuel 10, original node 1176056, the whole prefixCache at depth 11 and code 84804, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-84817-1177225", "unmarked_context_11_84817_1177225", "Unmarked parent at depth 11, code 84817",
                "The frontier Boolean is false at remaining fuel 10, original node 1177225, the whole prefixCache at depth 11 and code 84817, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84804-1176056", "node_context_11_84804_1176056", "Original split at fuel 10 and node 1176056",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1175939, 1175993, 1176055. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-84817-1177225", "node_context_11_84817_1177225", "Original split at fuel 10 and node 1177225",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1177160, 170504, 1177191, 1177224. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-339219-1176055", "context_12_339219_1176055", "Context at depth 12, code 339219, node 1176055",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 339219 and original node 1176055, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-339272-1177247", "context_12_339272_1177247", "Context at depth 12, code 339272, node 1177247",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 339272 and original node 1177247, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
