using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1100Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1100.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1100",
        H("Original frontier context coverage 1100"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 45 exact cut-selection equations, and 19 literal split equations paired with 19 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-52804", "selected_cut_52804", "Selected cut at depth 8, code 4732, node 1553253",
                "At remaining fuel 13 and original index 1553253, selection on the full partial prefix of depth 8 and code 4732 returns the complete row with depth 8, base-four code 4732, original node 1553253, kind 2, reserved field 0, 3517 subtree occurrences and completion domain 16777216. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-52848", "selected_cut_52848", "Selected cut at depth 7, code 1215, node 1557334",
                "At remaining fuel 14 and original index 1557334, selection on the full partial prefix of depth 7 and code 1215 returns the complete row with depth 7, base-four code 1215, original node 1557334, kind 2, reserved field 0, 925 subtree occurrences and completion domain 67108864. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-8-4731-1553052", "unmarked_context_8_4731_1553052", "Unmarked parent at depth 8, code 4731",
                "The frontier Boolean is false at remaining fuel 13, original node 1553052, the whole prefixCache at depth 8 and code 4731, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-4-18-1557337", "unmarked_context_4_18_1557337", "Unmarked parent at depth 4, code 18",
                "The frontier Boolean is false at remaining fuel 17, original node 1557337, the whole prefixCache at depth 4 and code 18, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-8-4731-1553052", "node_context_8_4731_1553052", "Original split at fuel 13 and node 1553052",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 1552817, 1552933, 1553038, 1553051. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-4-18-1557337", "node_context_4_18_1557337", "Original split at fuel 17 and node 1557337",
                "The complete original decoder output is the split at coordinate 4, with value children 0 through 3 respectively at original indices 1544921, 1553854, 1554773, 1557336. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-8-4731-1553052", "context_8_4731_1553052", "Context at depth 8, code 4731, node 1553052",
                "The conclusion is adaptive Accepted at the exact depth 8, full base-four code 4731 and original node 1553052, hence remaining fuel 13, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_9_18924_1552817, context_9_18925_1552933, context_9_18926_1553038, context_9_18927_1553051.", DescribeRole.Theorem),
            Node("context-4-18-1557337", "context_4_18_1557337", "Context at depth 4, code 18, node 1557337",
                "The conclusion is adaptive Accepted at the exact depth 4, full base-four code 18 and original node 1557337, hence remaining fuel 17, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_5_72_1544921, context_5_73_1553854, context_5_74_1554773, context_5_75_1557336.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
