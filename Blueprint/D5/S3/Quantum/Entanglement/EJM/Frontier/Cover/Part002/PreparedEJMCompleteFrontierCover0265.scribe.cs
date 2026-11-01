using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0265Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0265.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0265",
        H("Original frontier context coverage 0265"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-12723", "selected_cut_12723", "Selected cut at depth 13, code 105498, node 335271",
                "At remaining fuel 8 and original index 335271, selection on the full partial prefix of depth 13 and code 105498 returns the complete row with depth 13, base-four code 105498, original node 335271, kind 2, reserved field 0, 2397 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-12769", "selected_cut_12769", "Selected cut at depth 13, code 105535, node 337053",
                "At remaining fuel 8 and original index 337053, selection on the full partial prefix of depth 13 and code 105535 returns the complete row with depth 13, base-four code 105535, original node 337053, kind 2, reserved field 0, 1309 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26374-335289", "unmarked_context_12_26374_335289", "Unmarked parent at depth 12, code 26374",
                "The frontier Boolean is false at remaining fuel 9, original node 335289, the whole prefixCache at depth 12 and code 26374, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-1648-337056", "unmarked_context_10_1648_337056", "Unmarked parent at depth 10, code 1648",
                "The frontier Boolean is false at remaining fuel 11, original node 337056, the whole prefixCache at depth 10 and code 1648, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26374-335289", "node_context_12_26374_335289", "Original split at fuel 9 and node 335289",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 335145, 335227, 335271, 335288. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-1648-337056", "node_context_10_1648_337056", "Original split at fuel 11 and node 337056",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 334877, 335461, 336307, 337055. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-105498-335271", "context_13_105498_335271", "Context at depth 13, code 105498, node 335271",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 105498 and original node 335271, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-1648-337056", "context_10_1648_337056", "Context at depth 10, code 1648, node 337056",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 1648 and original node 337056, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_6592_334877, context_11_6593_335461, context_11_6594_336307, context_11_6595_337055.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
