using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0730Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0730.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0730",
        H("Original frontier context coverage 0730"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-35043", "selected_cut_35043", "Selected cut at depth 11, code 70836, node 916738",
                "At remaining fuel 10 and original index 916738, selection on the full partial prefix of depth 11 and code 70836 returns the complete row with depth 11, base-four code 70836, original node 916738, kind 2, reserved field 0, 1697 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-35089", "selected_cut_35089", "Selected cut at depth 12, code 284032, node 918545",
                "At remaining fuel 9 and original index 918545, selection on the full partial prefix of depth 12 and code 284032 returns the complete row with depth 12, base-four code 284032, original node 918545, kind 2, reserved field 0, 1461 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-17708-916723", "unmarked_context_10_17708_916723", "Unmarked parent at depth 10, code 17708",
                "The frontier Boolean is false at remaining fuel 11, original node 916723, the whole prefixCache at depth 10 and code 17708, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-4437-918506", "unmarked_context_9_4437_918506", "Unmarked parent at depth 9, code 4437",
                "The frontier Boolean is false at remaining fuel 12, original node 918506, the whole prefixCache at depth 9 and code 4437, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-17708-916723", "node_context_10_17708_916723", "Original split at fuel 11 and node 916723",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 907917, 916672, 916692, 916722. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-4437-918506", "node_context_9_4437_918506", "Original split at fuel 12 and node 918506",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 918261, 893098, 918505, 3440. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-17708-916723", "context_10_17708_916723", "Context at depth 10, code 17708, node 916723",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 17708 and original node 916723, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_70832_907917, context_11_70833_916672, context_11_70834_916692, context_11_70835_916722.", DescribeRole.Theorem),
            Node("context-12-284032-918545", "context_12_284032_918545", "Context at depth 12, code 284032, node 918545",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 284032 and original node 918545, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
