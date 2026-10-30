using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1009Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1009.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1009",
        H("Original frontier context coverage 1009"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-48436", "selected_cut_48436", "Selected cut at depth 10, code 23515, node 1359028",
                "At remaining fuel 11 and original index 1359028, selection on the full partial prefix of depth 10 and code 23515 returns the complete row with depth 10, base-four code 23515, original node 1359028, kind 2, reserved field 0, 2913 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-48484", "selected_cut_48484", "Selected cut at depth 12, code 376375, node 1360646",
                "At remaining fuel 9 and original index 1360646, selection on the full partial prefix of depth 12 and code 376375 returns the complete row with depth 12, base-four code 376375, original node 1360646, kind 2, reserved field 0, 2065 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-5878-1359029", "unmarked_context_9_5878_1359029", "Unmarked parent at depth 9, code 5878",
                "The frontier Boolean is false at remaining fuel 12, original node 1359029, the whole prefixCache at depth 9 and code 5878, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-94092-1360479", "unmarked_context_11_94092_1360479", "Unmarked parent at depth 11, code 94092",
                "The frontier Boolean is false at remaining fuel 10, original node 1360479, the whole prefixCache at depth 11 and code 94092, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-5878-1359029", "node_context_9_5878_1359029", "Original split at fuel 12 and node 1359029",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1358818, 1358936, 1358976, 1359028. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-94092-1360479", "node_context_11_94092_1360479", "Original split at fuel 10 and node 1360479",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1255011, 1360410, 1360445, 1360478. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-23515-1359028", "context_10_23515_1359028", "Context at depth 10, code 23515, node 1359028",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 23515 and original node 1359028, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-376375-1360646", "context_12_376375_1360646", "Context at depth 12, code 376375, node 1360646",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 376375 and original node 1360646, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
