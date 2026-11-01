using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1003Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1003.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1003",
        H("Original frontier context coverage 1003"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-48147", "selected_cut_48147", "Selected cut at depth 11, code 93840, node 1350006",
                "At remaining fuel 10 and original index 1350006, selection on the full partial prefix of depth 11 and code 93840 returns the complete row with depth 11, base-four code 93840, original node 1350006, kind 2, reserved field 0, 3661 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-48195", "selected_cut_48195", "Selected cut at depth 12, code 375567, node 903806",
                "At remaining fuel 9 and original index 903806, selection on the full partial prefix of depth 12 and code 375567 returns the complete row with depth 12, base-four code 375567, original node 903806, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-93841-1350123", "unmarked_context_11_93841_1350123", "Unmarked parent at depth 11, code 93841",
                "The frontier Boolean is false at remaining fuel 10, original node 1350123, the whole prefixCache at depth 11 and code 93841, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-93891-1351412", "unmarked_context_11_93891_1351412", "Unmarked parent at depth 11, code 93891",
                "The frontier Boolean is false at remaining fuel 10, original node 1351412, the whole prefixCache at depth 11 and code 93891, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-93841-1350123", "node_context_11_93841_1350123", "Original split at fuel 10 and node 1350123",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1350050, 1257136, 1350089, 1350122. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-93891-1351412", "node_context_11_93891_1351412", "Original split at fuel 10 and node 1351412",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 1351342, 1351411, 903806. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-93840-1350006", "context_11_93840_1350006", "Context at depth 11, code 93840, node 1350006",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 93840 and original node 1350006, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-93891-1351412", "context_11_93891_1351412", "Context at depth 11, code 93891, node 1351412",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 93891 and original node 1351412, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_375564_448748, context_12_375565_1351342, context_12_375566_1351411, context_12_375567_903806.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
