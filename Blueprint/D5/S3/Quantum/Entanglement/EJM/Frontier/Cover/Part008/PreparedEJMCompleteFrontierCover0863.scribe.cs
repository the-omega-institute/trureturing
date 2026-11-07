using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0863Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0863.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0863",
        H("Original frontier context coverage 0863"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-41426", "selected_cut_41426", "Selected cut at depth 12, code 335906, node 1133023",
                "At remaining fuel 9 and original index 1133023, selection on the full partial prefix of depth 12 and code 335906 returns the complete row with depth 12, base-four code 335906, original node 1133023, kind 2, reserved field 0, 1901 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-41474", "selected_cut_41474", "Selected cut at depth 12, code 335975, node 1134022",
                "At remaining fuel 9 and original index 1134022, selection on the full partial prefix of depth 12 and code 335975 returns the complete row with depth 12, base-four code 335975, original node 1134022, kind 2, reserved field 0, 1653 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-83976-1133044", "unmarked_context_11_83976_1133044", "Unmarked parent at depth 11, code 83976",
                "The frontier Boolean is false at remaining fuel 10, original node 1133044, the whole prefixCache at depth 11 and code 83976, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-83992-1133943", "unmarked_context_11_83992_1133943", "Unmarked parent at depth 11, code 83992",
                "The frontier Boolean is false at remaining fuel 10, original node 1133943, the whole prefixCache at depth 11 and code 83992, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-83976-1133044", "node_context_11_83976_1133044", "Original split at fuel 10 and node 1133044",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1132997, 1133023, 1133043. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-83992-1133943", "node_context_11_83992_1133943", "Original split at fuel 10 and node 1133943",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 985390, 1133903, 1133926, 1133942. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-335906-1133023", "context_12_335906_1133023", "Context at depth 12, code 335906, node 1133023",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 335906 and original node 1133023, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-335975-1134022", "context_12_335975_1134022", "Context at depth 12, code 335975, node 1134022",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 335975 and original node 1134022, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
