using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0019Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0019.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0019",
        H("Original frontier context coverage 0019"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-00913", "selected_cut_00913", "Selected cut at depth 12, code 4165, node 36798",
                "At remaining fuel 9 and original index 36798, selection on the full partial prefix of depth 12 and code 4165 returns the complete row with depth 12, base-four code 4165, original node 36798, kind 2, reserved field 0, 2789 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-00961", "selected_cut_00961", "Selected cut at depth 12, code 4195, node 37926",
                "At remaining fuel 9 and original index 37926, selection on the full partial prefix of depth 12 and code 4195 returns the complete row with depth 12, base-four code 4195, original node 37926, kind 2, reserved field 0, 2117 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-4166-36904", "unmarked_context_12_4166_36904", "Unmarked parent at depth 12, code 4166",
                "The frontier Boolean is false at remaining fuel 9, original node 36904, the whole prefixCache at depth 12 and code 4166, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-261-37817", "unmarked_context_10_261_37817", "Unmarked parent at depth 10, code 261",
                "The frontier Boolean is false at remaining fuel 11, original node 37817, the whole prefixCache at depth 10 and code 261, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-4166-36904", "node_context_12_4166_36904", "Original split at fuel 9 and node 36904",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 36850, 36886, 36903. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-261-37817", "node_context_10_261_37817", "Original split at fuel 11 and node 37817",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 37310, 37482, 37816, 1736. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-4165-36798", "context_12_4165_36798", "Context at depth 12, code 4165, node 36798",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 4165 and original node 36798, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-4195-37926", "context_12_4195_37926", "Context at depth 12, code 4195, node 37926",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 4195 and original node 37926, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
