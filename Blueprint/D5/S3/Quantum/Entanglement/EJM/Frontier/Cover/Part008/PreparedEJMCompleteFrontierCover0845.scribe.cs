using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0845Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0845.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0845",
        H("Original frontier context coverage 0845"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 46 exact cut-selection equations, and 18 literal split equations paired with 18 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-40565", "selected_cut_40565", "Selected cut at depth 12, code 310127, node 903806",
                "At remaining fuel 9 and original index 903806, selection on the full partial prefix of depth 12 and code 310127 returns the complete row with depth 12, base-four code 310127, original node 903806, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-40610", "selected_cut_40610", "Selected cut at depth 10, code 19391, node 1105205",
                "At remaining fuel 11 and original index 1105205, selection on the full partial prefix of depth 10 and code 19391 returns the complete row with depth 10, base-four code 19391, original node 1105205, kind 2, reserved field 0, 617 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-77531-1104047", "unmarked_context_11_77531_1104047", "Unmarked parent at depth 11, code 77531",
                "The frontier Boolean is false at remaining fuel 10, original node 1104047, the whole prefixCache at depth 11 and code 77531, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-8-1211-1105207", "unmarked_context_8_1211_1105207", "Unmarked parent at depth 8, code 1211",
                "The frontier Boolean is false at remaining fuel 13, original node 1105207, the whole prefixCache at depth 8 and code 1211, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-77531-1104047", "node_context_11_77531_1104047", "Original split at fuel 10 and node 1104047",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1103990, 1104019, 1104046, 903806. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-8-1211-1105207", "node_context_8_1211_1105207", "Original split at fuel 13 and node 1105207",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 1103121, 1104386, 1104965, 1105206. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-310127-903806", "context_12_310127_903806", "Context at depth 12, code 310127, node 903806",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 310127 and original node 903806, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-8-1211-1105207", "context_8_1211_1105207", "Context at depth 8, code 1211, node 1105207",
                "The conclusion is adaptive Accepted at the exact depth 8, full base-four code 1211 and original node 1105207, hence remaining fuel 13, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_9_4844_1103121, context_9_4845_1104386, context_9_4846_1104965, context_9_4847_1105206.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
