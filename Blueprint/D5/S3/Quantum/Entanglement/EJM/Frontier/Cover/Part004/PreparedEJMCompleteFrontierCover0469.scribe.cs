using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0469Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0469.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0469",
        H("Original frontier context coverage 0469"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-22516", "selected_cut_22516", "Selected cut at depth 12, code 75706, node 572999",
                "At remaining fuel 9 and original index 572999, selection on the full partial prefix of depth 12 and code 75706 returns the complete row with depth 12, base-four code 75706, original node 572999, kind 2, reserved field 0, 1413 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-22562", "selected_cut_22562", "Selected cut at depth 13, code 303179, node 573970",
                "At remaining fuel 8 and original index 573970, selection on the full partial prefix of depth 13 and code 303179 returns the complete row with depth 13, base-four code 303179, original node 573970, kind 2, reserved field 0, 737 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-18926-573016", "unmarked_context_11_18926_573016", "Unmarked parent at depth 11, code 18926",
                "The frontier Boolean is false at remaining fuel 10, original node 573016, the whole prefixCache at depth 11 and code 18926, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-75793-573896", "unmarked_context_12_75793_573896", "Unmarked parent at depth 12, code 75793",
                "The frontier Boolean is false at remaining fuel 9, original node 573896, the whole prefixCache at depth 12 and code 75793, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-18926-573016", "node_context_11_18926_573016", "Original split at fuel 10 and node 573016",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 572950, 572967, 572999, 573015. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-75793-573896", "node_context_12_75793_573896", "Original split at fuel 9 and node 573896",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 573854, 573874, 573890, 573895. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-75706-572999", "context_12_75706_572999", "Context at depth 12, code 75706, node 572999",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 75706 and original node 572999, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-303179-573970", "context_13_303179_573970", "Context at depth 13, code 303179, node 573970",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 303179 and original node 573970, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
