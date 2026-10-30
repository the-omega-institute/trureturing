using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0026Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0026.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0026",
        H("Original frontier context coverage 0026"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-01251", "selected_cut_01251", "Selected cut at depth 13, code 17832, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 17832 returns the complete row with depth 13, base-four code 17832, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-01297", "selected_cut_01297", "Selected cut at depth 12, code 4501, node 47729",
                "At remaining fuel 9 and original index 47729, selection on the full partial prefix of depth 12 and code 4501 returns the complete row with depth 12, base-four code 4501, original node 47729, kind 2, reserved field 0, 2553 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-4457-46208", "unmarked_context_12_4457_46208", "Unmarked parent at depth 12, code 4457",
                "The frontier Boolean is false at remaining fuel 9, original node 46208, the whole prefixCache at depth 12 and code 4457, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-1124-47613", "unmarked_context_11_1124_47613", "Unmarked parent at depth 11, code 1124",
                "The frontier Boolean is false at remaining fuel 10, original node 47613, the whole prefixCache at depth 11 and code 1124, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-4457-46208", "node_context_12_4457_46208", "Original split at fuel 9 and node 46208",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 46165, 46191, 46207. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-1124-47613", "node_context_11_1124_47613", "Original split at fuel 10 and node 47613",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 47501, 47538, 47573, 47612. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-4457-46208", "context_12_4457_46208", "Context at depth 12, code 4457, node 46208",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 4457 and original node 46208, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_17828_3444, context_13_17829_46165, context_13_17830_46191, context_13_17831_46207.", DescribeRole.Theorem),
            Node("context-12-4501-47729", "context_12_4501_47729", "Context at depth 12, code 4501, node 47729",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 4501 and original node 47729, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
