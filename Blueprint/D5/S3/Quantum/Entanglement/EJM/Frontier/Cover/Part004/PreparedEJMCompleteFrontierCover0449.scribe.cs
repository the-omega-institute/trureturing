using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0449Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0449.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0449",
        H("Original frontier context coverage 0449"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-21555", "selected_cut_21555", "Selected cut at depth 12, code 75084, node 551394",
                "At remaining fuel 9 and original index 551394, selection on the full partial prefix of depth 12 and code 75084 returns the complete row with depth 12, base-four code 75084, original node 551394, kind 2, reserved field 0, 4021 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-21601", "selected_cut_21601", "Selected cut at depth 13, code 300415, node 552102",
                "At remaining fuel 8 and original index 552102, selection on the full partial prefix of depth 13 and code 300415 returns the complete row with depth 13, base-four code 300415, original node 552102, kind 2, reserved field 0, 973 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-18770-551337", "unmarked_context_11_18770_551337", "Unmarked parent at depth 11, code 18770",
                "The frontier Boolean is false at remaining fuel 10, original node 551337, the whole prefixCache at depth 11 and code 18770, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-4693-552105", "unmarked_context_10_4693_552105", "Unmarked parent at depth 10, code 4693",
                "The frontier Boolean is false at remaining fuel 11, original node 552105, the whole prefixCache at depth 10 and code 4693, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-18770-551337", "node_context_11_18770_551337", "Original split at fuel 10 and node 551337",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 551145, 551197, 551257, 551336. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-4693-552105", "node_context_10_4693_552105", "Original split at fuel 11 and node 552105",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 551736, 451541, 551928, 552104. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-18770-551337", "context_11_18770_551337", "Context at depth 11, code 18770, node 551337",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 18770 and original node 551337, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_75080_551145, context_12_75081_551197, context_12_75082_551257, context_12_75083_551336.", DescribeRole.Theorem),
            Node("context-10-4693-552105", "context_10_4693_552105", "Context at depth 10, code 4693, node 552105",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 4693 and original node 552105, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_18772_551736, context_11_18773_451541, context_11_18774_551928, context_11_18775_552104.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
