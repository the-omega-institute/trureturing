using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0646Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0646.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0646",
        H("Original frontier context coverage 0646"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-31011", "selected_cut_31011", "Selected cut at depth 13, code 421971, node 789806",
                "At remaining fuel 8 and original index 789806, selection on the full partial prefix of depth 13 and code 421971 returns the complete row with depth 13, base-four code 421971, original node 789806, kind 2, reserved field 0, 821 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-31058", "selected_cut_31058", "Selected cut at depth 13, code 422021, node 790972",
                "At remaining fuel 8 and original index 790972, selection on the full partial prefix of depth 13 and code 422021 returns the complete row with depth 13, base-four code 422021, original node 790972, kind 2, reserved field 0, 2089 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-105492-789807", "unmarked_context_12_105492_789807", "Unmarked parent at depth 12, code 105492",
                "The frontier Boolean is false at remaining fuel 9, original node 789807, the whole prefixCache at depth 12 and code 105492, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-6593-790887", "unmarked_context_10_6593_790887", "Unmarked parent at depth 10, code 6593",
                "The frontier Boolean is false at remaining fuel 11, original node 790887, the whole prefixCache at depth 10 and code 6593, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-105492-789807", "node_context_12_105492_789807", "Original split at fuel 9 and node 789807",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 789718, 789763, 789794, 789806. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-6593-790887", "node_context_10_6593_790887", "Original split at fuel 11 and node 790887",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 789695, 790142, 790534, 790886. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-421971-789806", "context_13_421971_789806", "Context at depth 13, code 421971, node 789806",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 421971 and original node 789806, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-422021-790972", "context_13_422021_790972", "Context at depth 13, code 422021, node 790972",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 422021 and original node 790972, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
