using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0575Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0575.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0575",
        H("Original frontier context coverage 0575"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-27603", "selected_cut_27603", "Selected cut at depth 13, code 366801, node 697389",
                "At remaining fuel 8 and original index 697389, selection on the full partial prefix of depth 13 and code 366801 returns the complete row with depth 13, base-four code 366801, original node 697389, kind 2, reserved field 0, 1817 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-27650", "selected_cut_27650", "Selected cut at depth 13, code 366884, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 366884 returns the complete row with depth 13, base-four code 366884, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-91700-697408", "unmarked_context_12_91700_697408", "Unmarked parent at depth 12, code 91700",
                "The frontier Boolean is false at remaining fuel 9, original node 697408, the whole prefixCache at depth 12 and code 91700, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-22929-698452", "unmarked_context_11_22929_698452", "Unmarked parent at depth 11, code 22929",
                "The frontier Boolean is false at remaining fuel 10, original node 698452, the whole prefixCache at depth 11 and code 22929, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-91700-697408", "node_context_12_91700_697408", "Original split at fuel 9 and node 697408",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 697353, 697389, 697402, 697407. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-22929-698452", "node_context_11_22929_698452", "Original split at fuel 10 and node 698452",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 698345, 170504, 698393, 698451. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-366801-697389", "context_13_366801_697389", "Context at depth 13, code 366801, node 697389",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 366801 and original node 697389, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-366884-3444", "context_13_366884_3444", "Context at depth 13, code 366884, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 366884 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
