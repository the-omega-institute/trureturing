using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0848Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0848.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0848",
        H("Original frontier context coverage 0848"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-40706", "selected_cut_40706", "Selected cut at depth 12, code 331802, node 1108410",
                "At remaining fuel 9 and original index 1108410, selection on the full partial prefix of depth 12 and code 331802 returns the complete row with depth 12, base-four code 331802, original node 1108410, kind 2, reserved field 0, 1949 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-40754", "selected_cut_40754", "Selected cut at depth 12, code 332318, node 1110440",
                "At remaining fuel 9 and original index 1110440, selection on the full partial prefix of depth 12 and code 332318 returns the complete row with depth 12, base-four code 332318, original node 1110440, kind 2, reserved field 0, 2361 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-82950-1108463", "unmarked_context_11_82950_1108463", "Unmarked parent at depth 11, code 82950",
                "The frontier Boolean is false at remaining fuel 10, original node 1108463, the whole prefixCache at depth 11 and code 82950, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-83078-1110343", "unmarked_context_11_83078_1110343", "Unmarked parent at depth 11, code 83078",
                "The frontier Boolean is false at remaining fuel 10, original node 1110343, the whole prefixCache at depth 11 and code 83078, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-82950-1108463", "node_context_11_82950_1108463", "Original split at fuel 10 and node 1108463",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1108376, 1108410, 1108462. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-83078-1110343", "node_context_11_83078_1110343", "Original split at fuel 10 and node 1110343",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1110271, 893903, 1110342. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-331802-1108410", "context_12_331802_1108410", "Context at depth 12, code 331802, node 1108410",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 331802 and original node 1108410, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-332318-1110440", "context_12_332318_1110440", "Context at depth 12, code 332318, node 1110440",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 332318 and original node 1110440, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
