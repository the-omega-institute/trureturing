using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0025Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0025.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0025",
        H("Original frontier context coverage 0025"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-01202", "selected_cut_01202", "Selected cut at depth 13, code 17753, node 45174",
                "At remaining fuel 8 and original index 45174, selection on the full partial prefix of depth 13 and code 17753 returns the complete row with depth 13, base-four code 17753, original node 45174, kind 2, reserved field 0, 2177 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-01250", "selected_cut_01250", "Selected cut at depth 13, code 17831, node 46207",
                "At remaining fuel 8 and original index 46207, selection on the full partial prefix of depth 13 and code 17831 returns the complete row with depth 13, base-four code 17831, original node 46207, kind 2, reserved field 0, 1345 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-4438-45225", "unmarked_context_12_4438_45225", "Unmarked parent at depth 12, code 4438",
                "The frontier Boolean is false at remaining fuel 9, original node 45225, the whole prefixCache at depth 12 and code 4438, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-1113-46101", "unmarked_context_11_1113_46101", "Unmarked parent at depth 11, code 1113",
                "The frontier Boolean is false at remaining fuel 10, original node 46101, the whole prefixCache at depth 11 and code 1113, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-4438-45225", "node_context_12_4438_45225", "Original split at fuel 9 and node 45225",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 45174, 45203, 45224. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-1113-46101", "node_context_11_1113_46101", "Original split at fuel 10 and node 46101",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 45853, 45970, 46039, 46100. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-17753-45174", "context_13_17753_45174", "Context at depth 13, code 17753, node 45174",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 17753 and original node 45174, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-17831-46207", "context_13_17831_46207", "Context at depth 13, code 17831, node 46207",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 17831 and original node 46207, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
