using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0967Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0967.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0967",
        H("Original frontier context coverage 0967"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 50 exact cut-selection equations, and 14 literal split equations paired with 14 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-46418", "selected_cut_46418", "Selected cut at depth 11, code 92672, node 434745",
                "At remaining fuel 10 and original index 434745, selection on the full partial prefix of depth 11 and code 92672 returns the complete row with depth 11, base-four code 92672, original node 434745, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-46467", "selected_cut_46467", "Selected cut at depth 12, code 370743, node 1295894",
                "At remaining fuel 9 and original index 1295894, selection on the full partial prefix of depth 12 and code 370743 returns the complete row with depth 12, base-four code 370743, original node 1295894, kind 2, reserved field 0, 2901 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-92673-1294322", "unmarked_context_11_92673_1294322", "Unmarked parent at depth 11, code 92673",
                "The frontier Boolean is false at remaining fuel 10, original node 1294322, the whole prefixCache at depth 11 and code 92673, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-92684-1295721", "unmarked_context_11_92684_1295721", "Unmarked parent at depth 11, code 92684",
                "The frontier Boolean is false at remaining fuel 10, original node 1295721, the whole prefixCache at depth 11 and code 92684, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-92673-1294322", "node_context_11_92673_1294322", "Original split at fuel 10 and node 1294322",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 34034, 1294249, 1294321. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-92684-1295721", "node_context_11_92684_1295721", "Original split at fuel 10 and node 1295721",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 985390, 1295645, 1295681, 1295720. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-92672-434745", "context_11_92672_434745", "Context at depth 11, code 92672, node 434745",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 92672 and original node 434745, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-370743-1295894", "context_12_370743_1295894", "Context at depth 12, code 370743, node 1295894",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 370743 and original node 1295894, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
