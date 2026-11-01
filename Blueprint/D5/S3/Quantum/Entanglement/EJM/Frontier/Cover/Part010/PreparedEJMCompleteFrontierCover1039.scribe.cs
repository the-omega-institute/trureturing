using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1039Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1039.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1039",
        H("Original frontier context coverage 1039"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-49876", "selected_cut_49876", "Selected cut at depth 6, code 100, node 434744",
                "At remaining fuel 15 and original index 434744, selection on the full partial prefix of depth 6 and code 100 returns the complete row with depth 6, base-four code 100, original node 434744, kind 1, reserved field 0, 1 subtree occurrences and completion domain 268435456. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-49922", "selected_cut_49922", "Selected cut at depth 12, code 419603, node 1417039",
                "At remaining fuel 9 and original index 1417039, selection on the full partial prefix of depth 12 and code 419603 returns the complete row with depth 12, base-four code 419603, original node 1417039, kind 2, reserved field 0, 2485 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-8-1599-1414756", "unmarked_context_8_1599_1414756", "Unmarked parent at depth 8, code 1599",
                "The frontier Boolean is false at remaining fuel 13, original node 1414756, the whole prefixCache at depth 8 and code 1599, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-104900-1417040", "unmarked_context_11_104900_1417040", "Unmarked parent at depth 11, code 104900",
                "The frontier Boolean is false at remaining fuel 10, original node 1417040, the whole prefixCache at depth 11 and code 104900, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-8-1599-1414756", "node_context_8_1599_1414756", "Original split at fuel 13 and node 1414756",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 1413973, 1414415, 1414669, 1414755. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-104900-1417040", "node_context_11_104900_1417040", "Original split at fuel 10 and node 1417040",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1415033, 1416906, 1416968, 1417039. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-8-1599-1414756", "context_8_1599_1414756", "Context at depth 8, code 1599, node 1414756",
                "The conclusion is adaptive Accepted at the exact depth 8, full base-four code 1599 and original node 1414756, hence remaining fuel 13, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_9_6396_1413973, context_9_6397_1414415, context_9_6398_1414669, context_9_6399_1414755.", DescribeRole.Theorem),
            Node("context-11-104900-1417040", "context_11_104900_1417040", "Context at depth 11, code 104900, node 1417040",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 104900 and original node 1417040, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_419600_1415033, context_12_419601_1416906, context_12_419602_1416968, context_12_419603_1417039.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
