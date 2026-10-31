using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0021Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0021.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0021",
        H("Original frontier context coverage 0021"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-01010", "selected_cut_01010", "Selected cut at depth 14, code 69668, node 40123",
                "At remaining fuel 7 and original index 40123, selection on the full partial prefix of depth 14 and code 69668 returns the complete row with depth 14, base-four code 69668, original node 40123, kind 2, reserved field 0, 1341 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-01056", "selected_cut_01056", "Selected cut at depth 12, code 4371, node 893",
                "At remaining fuel 9 and original index 893, selection on the full partial prefix of depth 12 and code 4371 returns the complete row with depth 12, base-four code 4371, original node 893, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-17416-40103", "unmarked_context_13_17416_40103", "Unmarked parent at depth 13, code 17416",
                "The frontier Boolean is false at remaining fuel 8, original node 40103, the whole prefixCache at depth 13 and code 17416, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-1092-41741", "unmarked_context_11_1092_41741", "Unmarked parent at depth 11, code 1092",
                "The frontier Boolean is false at remaining fuel 10, original node 41741, the whole prefixCache at depth 11 and code 1092, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-17416-40103", "node_context_13_17416_40103", "Original split at fuel 8 and node 40103",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 40031, 40054, 40078, 40102. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-1092-41741", "node_context_11_1092_41741", "Original split at fuel 10 and node 41741",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 41574, 41627, 41740, 893. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-17416-40103", "context_13_17416_40103", "Context at depth 13, code 17416, node 40103",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 17416 and original node 40103, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_14_69664_40031, context_14_69665_40054, context_14_69666_40078, context_14_69667_40102.", DescribeRole.Theorem),
            Node("context-11-1092-41741", "context_11_1092_41741", "Context at depth 11, code 1092, node 41741",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 1092 and original node 41741, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_4368_41574, context_12_4369_41627, context_12_4370_41740, context_12_4371_893.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
