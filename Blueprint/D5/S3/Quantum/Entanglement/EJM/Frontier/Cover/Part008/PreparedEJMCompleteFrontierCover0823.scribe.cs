using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0823Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0823.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0823",
        H("Original frontier context coverage 0823"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-39508", "selected_cut_39508", "Selected cut at depth 11, code 76828, node 1072054",
                "At remaining fuel 10 and original index 1072054, selection on the full partial prefix of depth 11 and code 76828 returns the complete row with depth 11, base-four code 76828, original node 1072054, kind 2, reserved field 0, 3049 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-39554", "selected_cut_39554", "Selected cut at depth 12, code 307487, node 1073546",
                "At remaining fuel 9 and original index 1073546, selection on the full partial prefix of depth 12 and code 307487 returns the complete row with depth 12, base-four code 307487, original node 1073546, kind 2, reserved field 0, 3057 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-76827-1071992", "unmarked_context_11_76827_1071992", "Unmarked parent at depth 11, code 76827",
                "The frontier Boolean is false at remaining fuel 10, original node 1071992, the whole prefixCache at depth 11 and code 76827, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-76871-1073547", "unmarked_context_11_76871_1073547", "Unmarked parent at depth 11, code 76871",
                "The frontier Boolean is false at remaining fuel 10, original node 1073547, the whole prefixCache at depth 11 and code 76871, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-76827-1071992", "node_context_11_76827_1071992", "Original split at fuel 10 and node 1071992",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1071908, 1071935, 1071968, 1071991. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-76871-1073547", "node_context_11_76871_1073547", "Original split at fuel 10 and node 1073547",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1073416, 1073455, 1073503, 1073546. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-76827-1071992", "context_11_76827_1071992", "Context at depth 11, code 76827, node 1071992",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 76827 and original node 1071992, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_307308_1071908, context_12_307309_1071935, context_12_307310_1071968, context_12_307311_1071991.", DescribeRole.Theorem),
            Node("context-11-76871-1073547", "context_11_76871_1073547", "Context at depth 11, code 76871, node 1073547",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 76871 and original node 1073547, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_307484_1073416, context_12_307485_1073455, context_12_307486_1073503, context_12_307487_1073546.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
