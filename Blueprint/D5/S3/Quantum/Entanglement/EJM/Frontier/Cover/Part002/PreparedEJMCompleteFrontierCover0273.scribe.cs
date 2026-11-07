using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0273Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0273.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0273",
        H("Original frontier context coverage 0273"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-13107", "selected_cut_13107", "Selected cut at depth 12, code 26496, node 345315",
                "At remaining fuel 9 and original index 345315, selection on the full partial prefix of depth 12 and code 26496 returns the complete row with depth 12, base-four code 26496, original node 345315, kind 2, reserved field 0, 2969 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-13154", "selected_cut_13154", "Selected cut at depth 12, code 26543, node 346780",
                "At remaining fuel 9 and original index 346780, selection on the full partial prefix of depth 12 and code 26543 returns the complete row with depth 12, base-four code 26543, original node 346780, kind 2, reserved field 0, 1789 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-413-345287", "unmarked_context_9_413_345287", "Unmarked parent at depth 9, code 413",
                "The frontier Boolean is false at remaining fuel 12, original node 345287, the whole prefixCache at depth 9 and code 413, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-1658-346782", "unmarked_context_10_1658_346782", "Unmarked parent at depth 10, code 1658",
                "The frontier Boolean is false at remaining fuel 11, original node 346782, the whole prefixCache at depth 10 and code 1658, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-413-345287", "node_context_9_413_345287", "Original split at fuel 12 and node 345287",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 342365, 343388, 344482, 345286. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-1658-346782", "node_context_10_1658_346782", "Original split at fuel 11 and node 346782",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 346531, 346605, 346679, 346781. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-9-413-345287", "context_9_413_345287", "Context at depth 9, code 413, node 345287",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 413 and original node 345287, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_1652_342365, context_10_1653_343388, context_10_1654_344482, context_10_1655_345286.", DescribeRole.Theorem),
            Node("context-10-1658-346782", "context_10_1658_346782", "Context at depth 10, code 1658, node 346782",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 1658 and original node 346782, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_6632_346531, context_11_6633_346605, context_11_6634_346679, context_11_6635_346781.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
