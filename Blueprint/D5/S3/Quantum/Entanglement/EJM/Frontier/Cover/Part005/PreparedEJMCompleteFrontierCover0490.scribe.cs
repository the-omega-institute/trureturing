using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0490Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0490.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0490",
        H("Original frontier context coverage 0490"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-23523", "selected_cut_23523", "Selected cut at depth 11, code 19122, node 595511",
                "At remaining fuel 10 and original index 595511, selection on the full partial prefix of depth 11 and code 19122 returns the complete row with depth 11, base-four code 19122, original node 595511, kind 2, reserved field 0, 2429 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-23570", "selected_cut_23570", "Selected cut at depth 13, code 306263, node 596618",
                "At remaining fuel 8 and original index 596618, selection on the full partial prefix of depth 13 and code 306263 returns the complete row with depth 13, base-four code 306263, original node 596618, kind 2, reserved field 0, 841 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-4780-595549", "unmarked_context_10_4780_595549", "Unmarked parent at depth 10, code 4780",
                "The frontier Boolean is false at remaining fuel 11, original node 595549, the whole prefixCache at depth 10 and code 4780, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-76565-596619", "unmarked_context_12_76565_596619", "Unmarked parent at depth 12, code 76565",
                "The frontier Boolean is false at remaining fuel 9, original node 596619, the whole prefixCache at depth 12 and code 76565, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-4780-595549", "node_context_10_4780_595549", "Original split at fuel 11 and node 595549",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 595454, 595490, 595511, 595548. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-76565-596619", "node_context_12_76565_596619", "Original split at fuel 9 and node 596619",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 596565, 596591, 596611, 596618. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-19122-595511", "context_11_19122_595511", "Context at depth 11, code 19122, node 595511",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 19122 and original node 595511, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-76565-596619", "context_12_76565_596619", "Context at depth 12, code 76565, node 596619",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 76565 and original node 596619, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_306260_596565, context_13_306261_596591, context_13_306262_596611, context_13_306263_596618.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
