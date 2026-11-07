using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0000Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0000.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0000",
        H("Original frontier context coverage 0000"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-00000", "selected_cut_00000", "Selected cut at depth 12, code 0, node 415",
                "At remaining fuel 9 and original index 415, selection on the full partial prefix of depth 12 and code 0 returns the complete row with depth 12, base-four code 0, original node 415, kind 2, reserved field 0, 2061 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-00048", "selected_cut_00048", "Selected cut at depth 13, code 1026, node 4966",
                "At remaining fuel 8 and original index 4966, selection on the full partial prefix of depth 13 and code 1026 returns the complete row with depth 13, base-four code 1026, original node 4966, kind 2, reserved field 0, 825 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-1-891", "unmarked_context_12_1_891", "Unmarked parent at depth 12, code 1",
                "The frontier Boolean is false at remaining fuel 9, original node 891, the whole prefixCache at depth 12 and code 1, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-13-1024-4780", "unmarked_context_13_1024_4780", "Unmarked parent at depth 13, code 1024",
                "The frontier Boolean is false at remaining fuel 8, original node 4780, the whole prefixCache at depth 13 and code 1024, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-1-891", "node_context_12_1_891", "Original split at fuel 9 and node 891",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 674, 788, 890, 414. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-13-1024-4780", "node_context_13_1024_4780", "Original split at fuel 8 and node 4780",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 4635, 4682, 4779, 291. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-0-415", "context_12_0_415", "Context at depth 12, code 0, node 415",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 0 and original node 415, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-1026-4966", "context_13_1026_4966", "Context at depth 13, code 1026, node 4966",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1026 and original node 4966, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
