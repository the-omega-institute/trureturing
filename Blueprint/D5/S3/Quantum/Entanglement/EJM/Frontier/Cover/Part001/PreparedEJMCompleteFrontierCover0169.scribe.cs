using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0169Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0169.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0169",
        H("Original frontier context coverage 0169"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-08115", "selected_cut_08115", "Selected cut at depth 13, code 91344, node 230364",
                "At remaining fuel 8 and original index 230364, selection on the full partial prefix of depth 13 and code 91344 returns the complete row with depth 13, base-four code 91344, original node 230364, kind 2, reserved field 0, 409 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-08162", "selected_cut_08162", "Selected cut at depth 13, code 91391, node 231103",
                "At remaining fuel 8 and original index 231103, selection on the full partial prefix of depth 13 and code 91391 returns the complete row with depth 13, base-four code 91391, original node 231103, kind 2, reserved field 0, 849 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-5708-230356", "unmarked_context_11_5708_230356", "Unmarked parent at depth 11, code 5708",
                "The frontier Boolean is false at remaining fuel 10, original node 230356, the whole prefixCache at depth 11 and code 5708, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-5711-231105", "unmarked_context_11_5711_231105", "Unmarked parent at depth 11, code 5711",
                "The frontier Boolean is false at remaining fuel 10, original node 231105, the whole prefixCache at depth 11 and code 5711, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-5708-230356", "node_context_11_5708_230356", "Original split at fuel 10 and node 230356",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 230120, 230177, 230268, 230355. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-5711-231105", "node_context_11_5711_231105", "Original split at fuel 10 and node 231105",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 230931, 230980, 231045, 231104. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-5708-230356", "context_11_5708_230356", "Context at depth 11, code 5708, node 230356",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 5708 and original node 230356, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_22832_230120, context_12_22833_230177, context_12_22834_230268, context_12_22835_230355.", DescribeRole.Theorem),
            Node("context-11-5711-231105", "context_11_5711_231105", "Context at depth 11, code 5711, node 231105",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 5711 and original node 231105, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_22844_230931, context_12_22845_230980, context_12_22846_231045, context_12_22847_231104.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
