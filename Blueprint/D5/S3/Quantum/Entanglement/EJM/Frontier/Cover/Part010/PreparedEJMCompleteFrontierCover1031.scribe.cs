using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1031Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1031.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1031",
        H("Original frontier context coverage 1031"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-49491", "selected_cut_49491", "Selected cut at depth 12, code 407826, node 1400621",
                "At remaining fuel 9 and original index 1400621, selection on the full partial prefix of depth 12 and code 407826 returns the complete row with depth 12, base-four code 407826, original node 1400621, kind 2, reserved field 0, 2065 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-49539", "selected_cut_49539", "Selected cut at depth 10, code 25503, node 1402374",
                "At remaining fuel 11 and original index 1402374, selection on the full partial prefix of depth 10 and code 25503 returns the complete row with depth 10, base-four code 25503, original node 1402374, kind 2, reserved field 0, 73 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-101956-1400669", "unmarked_context_11_101956_1400669", "Unmarked parent at depth 11, code 101956",
                "The frontier Boolean is false at remaining fuel 10, original node 1400669, the whole prefixCache at depth 11 and code 101956, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-6374-1402223", "unmarked_context_9_6374_1402223", "Unmarked parent at depth 9, code 6374",
                "The frontier Boolean is false at remaining fuel 12, original node 1402223, the whole prefixCache at depth 9 and code 6374, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-101956-1400669", "node_context_11_101956_1400669", "Original split at fuel 10 and node 1400669",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1400578, 1400621, 1400668. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-6374-1402223", "node_context_9_6374_1402223", "Original split at fuel 12 and node 1402223",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1402013, 1402124, 1402148, 1402222. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-407826-1400621", "context_12_407826_1400621", "Context at depth 12, code 407826, node 1400621",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 407826 and original node 1400621, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-25503-1402374", "context_10_25503_1402374", "Context at depth 10, code 25503, node 1402374",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 25503 and original node 1402374, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
