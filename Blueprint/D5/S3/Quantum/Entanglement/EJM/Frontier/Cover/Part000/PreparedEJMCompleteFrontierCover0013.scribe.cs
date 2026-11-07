using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0013Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0013.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0013",
        H("Original frontier context coverage 0013"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-00627", "selected_cut_00627", "Selected cut at depth 12, code 1560, node 26677",
                "At remaining fuel 9 and original index 26677, selection on the full partial prefix of depth 12 and code 1560 returns the complete row with depth 12, base-four code 1560, original node 26677, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-00673", "selected_cut_00673", "Selected cut at depth 13, code 6319, node 28653",
                "At remaining fuel 8 and original index 28653, selection on the full partial prefix of depth 13 and code 6319 returns the complete row with depth 13, base-four code 6319, original node 28653, kind 2, reserved field 0, 889 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-1559-27562", "unmarked_context_12_1559_27562", "Unmarked parent at depth 12, code 1559",
                "The frontier Boolean is false at remaining fuel 9, original node 27562, the whole prefixCache at depth 12 and code 1559, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-394-28655", "unmarked_context_11_394_28655", "Unmarked parent at depth 11, code 394",
                "The frontier Boolean is false at remaining fuel 10, original node 28655, the whole prefixCache at depth 11 and code 394, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-1559-27562", "node_context_12_1559_27562", "Original split at fuel 9 and node 27562",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 27425, 27478, 27534, 27561. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-394-28655", "node_context_11_394_28655", "Original split at fuel 10 and node 28655",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 26677, 3161, 26677, 28654. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-1559-27562", "context_12_1559_27562", "Context at depth 12, code 1559, node 27562",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 1559 and original node 27562, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_6236_27425, context_13_6237_27478, context_13_6238_27534, context_13_6239_27561.", DescribeRole.Theorem),
            Node("context-11-394-28655", "context_11_394_28655", "Context at depth 11, code 394, node 28655",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 394 and original node 28655, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_1576_26677, context_12_1577_3161, context_12_1578_26677, context_12_1579_28654.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
