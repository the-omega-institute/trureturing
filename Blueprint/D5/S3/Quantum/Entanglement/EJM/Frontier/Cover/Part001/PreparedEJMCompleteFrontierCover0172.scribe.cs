using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0172Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0172.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0172",
        H("Original frontier context coverage 0172"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-08259", "selected_cut_08259", "Selected cut at depth 13, code 91500, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 91500 returns the complete row with depth 13, base-four code 91500, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-08307", "selected_cut_08307", "Selected cut at depth 13, code 91566, node 233354",
                "At remaining fuel 8 and original index 233354, selection on the full partial prefix of depth 13 and code 91566 returns the complete row with depth 13, base-four code 91566, original node 233354, kind 2, reserved field 0, 2729 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-22875-232525", "unmarked_context_12_22875_232525", "Unmarked parent at depth 12, code 22875",
                "The frontier Boolean is false at remaining fuel 9, original node 232525, the whole prefixCache at depth 12 and code 22875, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-22889-233195", "unmarked_context_12_22889_233195", "Unmarked parent at depth 12, code 22889",
                "The frontier Boolean is false at remaining fuel 9, original node 233195, the whole prefixCache at depth 12 and code 22889, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-22875-232525", "node_context_12_22875_232525", "Original split at fuel 9 and node 232525",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 232482, 232512, 232524. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-22889-233195", "node_context_12_22889_233195", "Original split at fuel 9 and node 233195",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 233127, 233166, 233194. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-91500-3444", "context_13_91500_3444", "Context at depth 13, code 91500, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 91500 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-91566-233354", "context_13_91566_233354", "Context at depth 13, code 91566, node 233354",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 91566 and original node 233354, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
