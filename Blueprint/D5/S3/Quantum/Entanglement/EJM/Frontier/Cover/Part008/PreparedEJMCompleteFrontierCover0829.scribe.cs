using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0829Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0829.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0829",
        H("Original frontier context coverage 0829"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-39796", "selected_cut_39796", "Selected cut at depth 12, code 307828, node 1079936",
                "At remaining fuel 9 and original index 1079936, selection on the full partial prefix of depth 12 and code 307828 returns the complete row with depth 12, base-four code 307828, original node 1079936, kind 2, reserved field 0, 1721 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-39842", "selected_cut_39842", "Selected cut at depth 13, code 1231892, node 1081014",
                "At remaining fuel 8 and original index 1081014, selection on the full partial prefix of depth 13 and code 1231892 returns the complete row with depth 13, base-four code 1231892, original node 1081014, kind 2, reserved field 0, 2037 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-76956-1079913", "unmarked_context_11_76956_1079913", "Unmarked parent at depth 11, code 76956",
                "The frontier Boolean is false at remaining fuel 10, original node 1079913, the whole prefixCache at depth 11 and code 76956, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-8-1202-1080974", "unmarked_context_8_1202_1080974", "Unmarked parent at depth 8, code 1202",
                "The frontier Boolean is false at remaining fuel 13, original node 1080974, the whole prefixCache at depth 8 and code 1202, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-76956-1079913", "node_context_11_76956_1079913", "Original split at fuel 10 and node 1079913",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1079840, 1079863, 1079885, 1079912. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-8-1202-1080974", "node_context_8_1202_1080974", "Original split at fuel 13 and node 1080974",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 1078994, 1080161, 1080755, 1080973. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-76956-1079913", "context_11_76956_1079913", "Context at depth 11, code 76956, node 1079913",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 76956 and original node 1079913, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_307824_1079840, context_12_307825_1079863, context_12_307826_1079885, context_12_307827_1079912.", DescribeRole.Theorem),
            Node("context-13-1231892-1081014", "context_13_1231892_1081014", "Context at depth 13, code 1231892, node 1081014",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1231892 and original node 1081014, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
