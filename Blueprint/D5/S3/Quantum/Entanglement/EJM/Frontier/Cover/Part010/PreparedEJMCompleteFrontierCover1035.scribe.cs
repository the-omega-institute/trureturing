using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1035Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1035.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1035",
        H("Original frontier context coverage 1035"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-49683", "selected_cut_49683", "Selected cut at depth 11, code 102153, node 1407578",
                "At remaining fuel 10 and original index 1407578, selection on the full partial prefix of depth 11 and code 102153 returns the complete row with depth 11, base-four code 102153, original node 1407578, kind 2, reserved field 0, 3965 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-49731", "selected_cut_49731", "Selected cut at depth 12, code 408867, node 1409426",
                "At remaining fuel 9 and original index 1409426, selection on the full partial prefix of depth 12 and code 408867 returns the complete row with depth 12, base-four code 408867, original node 1409426, kind 2, reserved field 0, 1909 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-25538-1407694", "unmarked_context_10_25538_1407694", "Unmarked parent at depth 10, code 25538",
                "The frontier Boolean is false at remaining fuel 11, original node 1407694, the whole prefixCache at depth 10 and code 25538, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-25553-1409260", "unmarked_context_10_25553_1409260", "Unmarked parent at depth 10, code 25553",
                "The frontier Boolean is false at remaining fuel 11, original node 1409260, the whole prefixCache at depth 10 and code 25553, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-25538-1407694", "node_context_10_25538_1407694", "Original split at fuel 11 and node 1407694",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1407490, 1407578, 1407622, 1407693. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-25553-1409260", "node_context_10_25553_1409260", "Original split at fuel 11 and node 1409260",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1409117, 1407133, 1409195, 1409259. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-102153-1407578", "context_11_102153_1407578", "Context at depth 11, code 102153, node 1407578",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 102153 and original node 1407578, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-408867-1409426", "context_12_408867_1409426", "Context at depth 12, code 408867, node 1409426",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 408867 and original node 1409426, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
