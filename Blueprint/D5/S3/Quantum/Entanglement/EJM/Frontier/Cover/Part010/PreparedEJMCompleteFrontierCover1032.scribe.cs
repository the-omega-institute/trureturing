using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1032Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1032.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1032",
        H("Original frontier context coverage 1032"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-49540", "selected_cut_49540", "Selected cut at depth 11, code 102016, node 434745",
                "At remaining fuel 10 and original index 434745, selection on the full partial prefix of depth 11 and code 102016 returns the complete row with depth 11, base-four code 102016, original node 434745, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-49587", "selected_cut_49587", "Selected cut at depth 11, code 102045, node 1404182",
                "At remaining fuel 10 and original index 1404182, selection on the full partial prefix of depth 11 and code 102045 returns the complete row with depth 11, base-four code 102045, original node 1404182, kind 2, reserved field 0, 2937 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-6375-1402375", "unmarked_context_9_6375_1402375", "Unmarked parent at depth 9, code 6375",
                "The frontier Boolean is false at remaining fuel 12, original node 1402375, the whole prefixCache at depth 9 and code 6375, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-25510-1404074", "unmarked_context_10_25510_1404074", "Unmarked parent at depth 10, code 25510",
                "The frontier Boolean is false at remaining fuel 11, original node 1404074, the whole prefixCache at depth 10 and code 25510, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-6375-1402375", "node_context_9_6375_1402375", "Original split at fuel 12 and node 1402375",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1402288, 1402333, 1402365, 1402374. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-25510-1404074", "node_context_10_25510_1404074", "Original split at fuel 11 and node 1404074",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1403915, 1404006, 900587, 1404073. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-9-6375-1402375", "context_9_6375_1402375", "Context at depth 9, code 6375, node 1402375",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 6375 and original node 1402375, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_25500_1402288, context_10_25501_1402333, context_10_25502_1402365, context_10_25503_1402374.", DescribeRole.Theorem),
            Node("context-11-102045-1404182", "context_11_102045_1404182", "Context at depth 11, code 102045, node 1404182",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 102045 and original node 1404182, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
