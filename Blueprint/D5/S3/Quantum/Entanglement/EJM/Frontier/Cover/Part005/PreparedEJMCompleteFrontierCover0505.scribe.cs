using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0505Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0505.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0505",
        H("Original frontier context coverage 0505"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-24243", "selected_cut_24243", "Selected cut at depth 12, code 77067, node 604131",
                "At remaining fuel 9 and original index 604131, selection on the full partial prefix of depth 12 and code 77067 returns the complete row with depth 12, base-four code 77067, original node 604131, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-24291", "selected_cut_24291", "Selected cut at depth 13, code 308349, node 614405",
                "At remaining fuel 8 and original index 614405, selection on the full partial prefix of depth 13 and code 308349 returns the complete row with depth 13, base-four code 308349, original node 614405, kind 2, reserved field 0, 2441 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-19266-613324", "unmarked_context_11_19266_613324", "Unmarked parent at depth 11, code 19266",
                "The frontier Boolean is false at remaining fuel 10, original node 613324, the whole prefixCache at depth 11 and code 19266, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-77086-614355", "unmarked_context_12_77086_614355", "Unmarked parent at depth 12, code 77086",
                "The frontier Boolean is false at remaining fuel 9, original node 614355, the whole prefixCache at depth 12 and code 77086, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-19266-613324", "node_context_11_19266_613324", "Original split at fuel 10 and node 613324",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 613323, 524302, 604131. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-77086-614355", "node_context_12_77086_614355", "Original split at fuel 9 and node 614355",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 614297, 614326, 614346, 614354. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-77067-604131", "context_12_77067_604131", "Context at depth 12, code 77067, node 604131",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 77067 and original node 604131, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-308349-614405", "context_13_308349_614405", "Context at depth 13, code 308349, node 614405",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 308349 and original node 614405, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
