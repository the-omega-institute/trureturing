using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0435Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0435.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0435",
        H("Original frontier context coverage 0435"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-20883", "selected_cut_20883", "Selected cut at depth 13, code 298197, node 534573",
                "At remaining fuel 8 and original index 534573, selection on the full partial prefix of depth 13 and code 298197 returns the complete row with depth 13, base-four code 298197, original node 534573, kind 2, reserved field 0, 1357 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-20930", "selected_cut_20930", "Selected cut at depth 12, code 74609, node 536637",
                "At remaining fuel 9 and original index 536637, selection on the full partial prefix of depth 12 and code 74609 returns the complete row with depth 12, base-four code 74609, original node 536637, kind 2, reserved field 0, 2061 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-74549-534598", "unmarked_context_12_74549_534598", "Unmarked parent at depth 12, code 74549",
                "The frontier Boolean is false at remaining fuel 9, original node 534598, the whole prefixCache at depth 12 and code 74549, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-4662-536573", "unmarked_context_10_4662_536573", "Unmarked parent at depth 10, code 4662",
                "The frontier Boolean is false at remaining fuel 11, original node 536573, the whole prefixCache at depth 10 and code 4662, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-74549-534598", "node_context_12_74549_534598", "Original split at fuel 9 and node 534598",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 534553, 534573, 534586, 534597. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-4662-536573", "node_context_10_4662_536573", "Original split at fuel 11 and node 536573",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 536319, 536416, 536495, 536572. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-298197-534573", "context_13_298197_534573", "Context at depth 13, code 298197, node 534573",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 298197 and original node 534573, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-74609-536637", "context_12_74609_536637", "Context at depth 12, code 74609, node 536637",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 74609 and original node 536637, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
