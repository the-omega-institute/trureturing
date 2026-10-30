using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0119Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0119.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0119",
        H("Original frontier context coverage 0119"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-05713", "selected_cut_05713", "Selected cut at depth 12, code 20800, node 175609",
                "At remaining fuel 9 and original index 175609, selection on the full partial prefix of depth 12 and code 20800 returns the complete row with depth 12, base-four code 20800, original node 175609, kind 2, reserved field 0, 1385 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-05761", "selected_cut_05761", "Selected cut at depth 13, code 83311, node 176435",
                "At remaining fuel 8 and original index 176435, selection on the full partial prefix of depth 13 and code 83311 returns the complete row with depth 13, base-four code 83311, original node 176435, kind 2, reserved field 0, 945 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-20802-175744", "unmarked_context_12_20802_175744", "Unmarked parent at depth 12, code 20802",
                "The frontier Boolean is false at remaining fuel 9, original node 175744, the whole prefixCache at depth 12 and code 20802, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-5206-176437", "unmarked_context_11_5206_176437", "Unmarked parent at depth 11, code 5206",
                "The frontier Boolean is false at remaining fuel 10, original node 176437, the whole prefixCache at depth 11 and code 5206, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-20802-175744", "node_context_12_20802_175744", "Original split at fuel 9 and node 175744",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 175706, 175731, 175743. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-5206-176437", "node_context_11_5206_176437", "Original split at fuel 10 and node 176437",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 176268, 176336, 176385, 176436. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-20800-175609", "context_12_20800_175609", "Context at depth 12, code 20800, node 175609",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 20800 and original node 175609, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-5206-176437", "context_11_5206_176437", "Context at depth 11, code 5206, node 176437",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 5206 and original node 176437, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_20824_176268, context_12_20825_176336, context_12_20826_176385, context_12_20827_176436.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
