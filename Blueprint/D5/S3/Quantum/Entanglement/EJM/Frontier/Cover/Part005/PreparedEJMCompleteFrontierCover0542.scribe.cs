using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0542Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0542.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0542",
        H("Original frontier context coverage 0542"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-26019", "selected_cut_26019", "Selected cut at depth 13, code 354327, node 658263",
                "At remaining fuel 8 and original index 658263, selection on the full partial prefix of depth 13 and code 354327 returns the complete row with depth 13, base-four code 354327, original node 658263, kind 2, reserved field 0, 1197 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-26066", "selected_cut_26066", "Selected cut at depth 13, code 354380, node 660010",
                "At remaining fuel 8 and original index 660010, selection on the full partial prefix of depth 13 and code 354380 returns the complete row with depth 13, base-four code 354380, original node 660010, kind 2, reserved field 0, 3017 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-88581-658264", "unmarked_context_12_88581_658264", "Unmarked parent at depth 12, code 88581",
                "The frontier Boolean is false at remaining fuel 9, original node 658264, the whole prefixCache at depth 12 and code 88581, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-88594-659958", "unmarked_context_12_88594_659958", "Unmarked parent at depth 12, code 88594",
                "The frontier Boolean is false at remaining fuel 9, original node 659958, the whole prefixCache at depth 12 and code 88594, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-88581-658264", "node_context_12_88581_658264", "Original split at fuel 9 and node 658264",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 658119, 658204, 658224, 658263. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-88594-659958", "node_context_12_88594_659958", "Original split at fuel 9 and node 659958",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 659894, 659920, 659940, 659957. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-354327-658263", "context_13_354327_658263", "Context at depth 13, code 354327, node 658263",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 354327 and original node 658263, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-354380-660010", "context_13_354380_660010", "Context at depth 13, code 354380, node 660010",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 354380 and original node 660010, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
