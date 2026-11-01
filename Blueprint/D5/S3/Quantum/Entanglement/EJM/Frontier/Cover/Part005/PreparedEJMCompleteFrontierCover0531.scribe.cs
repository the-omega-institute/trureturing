using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0531Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0531.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0531",
        H("Original frontier context coverage 0531"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-25491", "selected_cut_25491", "Selected cut at depth 13, code 350307, node 645001",
                "At remaining fuel 8 and original index 645001, selection on the full partial prefix of depth 13 and code 350307 returns the complete row with depth 13, base-four code 350307, original node 645001, kind 2, reserved field 0, 865 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-25538", "selected_cut_25538", "Selected cut at depth 13, code 350384, node 646124",
                "At remaining fuel 8 and original index 646124, selection on the full partial prefix of depth 13 and code 350384 returns the complete row with depth 13, base-four code 350384, original node 646124, kind 2, reserved field 0, 585 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-87576-645002", "unmarked_context_12_87576_645002", "Unmarked parent at depth 12, code 87576",
                "The frontier Boolean is false at remaining fuel 9, original node 645002, the whole prefixCache at depth 12 and code 87576, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-21898-646114", "unmarked_context_11_21898_646114", "Unmarked parent at depth 11, code 21898",
                "The frontier Boolean is false at remaining fuel 10, original node 646114, the whole prefixCache at depth 11 and code 21898, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-87576-645002", "node_context_12_87576_645002", "Original split at fuel 9 and node 645002",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 644956, 644977, 644995, 645001. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-21898-646114", "node_context_11_21898_646114", "Original split at fuel 10 and node 646114",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 646015, 646062, 445248, 646113. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-350307-645001", "context_13_350307_645001", "Context at depth 13, code 350307, node 645001",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 350307 and original node 645001, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-350384-646124", "context_13_350384_646124", "Context at depth 13, code 350384, node 646124",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 350384 and original node 646124, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
