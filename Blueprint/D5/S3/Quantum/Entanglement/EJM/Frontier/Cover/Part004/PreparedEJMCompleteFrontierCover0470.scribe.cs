using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0470Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0470.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0470",
        H("Original frontier context coverage 0470"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-22563", "selected_cut_22563", "Selected cut at depth 13, code 303180, node 573997",
                "At remaining fuel 8 and original index 573997, selection on the full partial prefix of depth 13 and code 303180 returns the complete row with depth 13, base-four code 303180, original node 573997, kind 2, reserved field 0, 1325 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-22609", "selected_cut_22609", "Selected cut at depth 12, code 75811, node 574928",
                "At remaining fuel 9 and original index 574928, selection on the full partial prefix of depth 12 and code 75811 returns the complete row with depth 12, base-four code 75811, original node 574928, kind 2, reserved field 0, 3897 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-75794-573971", "unmarked_context_12_75794_573971", "Unmarked parent at depth 12, code 75794",
                "The frontier Boolean is false at remaining fuel 9, original node 573971, the whole prefixCache at depth 12 and code 75794, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-18952-574929", "unmarked_context_11_18952_574929", "Unmarked parent at depth 11, code 18952",
                "The frontier Boolean is false at remaining fuel 10, original node 574929, the whole prefixCache at depth 11 and code 18952, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-75794-573971", "node_context_12_75794_573971", "Original split at fuel 9 and node 573971",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 573925, 573946, 573964, 573970. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-18952-574929", "node_context_11_18952_574929", "Original split at fuel 10 and node 574929",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435790, 574819, 574874, 574928. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-75794-573971", "context_12_75794_573971", "Context at depth 12, code 75794, node 573971",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 75794 and original node 573971, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_303176_573925, context_13_303177_573946, context_13_303178_573964, context_13_303179_573970.", DescribeRole.Theorem),
            Node("context-11-18952-574929", "context_11_18952_574929", "Context at depth 11, code 18952, node 574929",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 18952 and original node 574929, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_75808_435790, context_12_75809_574819, context_12_75810_574874, context_12_75811_574928.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
