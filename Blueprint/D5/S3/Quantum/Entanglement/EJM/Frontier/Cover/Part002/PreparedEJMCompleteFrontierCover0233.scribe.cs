using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0233Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0233.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0233",
        H("Original frontier context coverage 0233"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-11187", "selected_cut_11187", "Selected cut at depth 12, code 25479, node 300185",
                "At remaining fuel 9 and original index 300185, selection on the full partial prefix of depth 12 and code 25479 returns the complete row with depth 12, base-four code 25479, original node 300185, kind 2, reserved field 0, 2753 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-11235", "selected_cut_11235", "Selected cut at depth 12, code 25527, node 301193",
                "At remaining fuel 9 and original index 301193, selection on the full partial prefix of depth 12 and code 25527 returns the complete row with depth 12, base-four code 25527, original node 301193, kind 2, reserved field 0, 1389 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-6369-300186", "unmarked_context_11_6369_300186", "Unmarked parent at depth 11, code 6369",
                "The frontier Boolean is false at remaining fuel 10, original node 300186, the whole prefixCache at depth 11 and code 6369, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-6380-301138", "unmarked_context_11_6380_301138", "Unmarked parent at depth 11, code 6380",
                "The frontier Boolean is false at remaining fuel 10, original node 301138, the whole prefixCache at depth 11 and code 6380, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-6369-300186", "node_context_11_6369_300186", "Original split at fuel 10 and node 300186",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 300104, 300131, 300160, 300185. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-6380-301138", "node_context_11_6380_301138", "Original split at fuel 10 and node 301138",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 301089, 301105, 301120, 301137. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-25479-300185", "context_12_25479_300185", "Context at depth 12, code 25479, node 300185",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25479 and original node 300185, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-25527-301193", "context_12_25527_301193", "Context at depth 12, code 25527, node 301193",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25527 and original node 301193, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
