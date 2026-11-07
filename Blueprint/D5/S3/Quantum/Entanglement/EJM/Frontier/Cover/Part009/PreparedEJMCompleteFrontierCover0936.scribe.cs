using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0936Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0936.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0936",
        H("Original frontier context coverage 0936"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-44931", "selected_cut_44931", "Selected cut at depth 11, code 88851, node 1239890",
                "At remaining fuel 10 and original index 1239890, selection on the full partial prefix of depth 11 and code 88851 returns the complete row with depth 11, base-four code 88851, original node 1239890, kind 2, reserved field 0, 3033 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-44978", "selected_cut_44978", "Selected cut at depth 12, code 355589, node 34034",
                "At remaining fuel 9 and original index 34034, selection on the full partial prefix of depth 12 and code 355589 returns the complete row with depth 12, base-four code 355589, original node 34034, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-22212-1239891", "unmarked_context_10_22212_1239891", "Unmarked parent at depth 10, code 22212",
                "The frontier Boolean is false at remaining fuel 11, original node 1239891, the whole prefixCache at depth 10 and code 22212, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-8-1388-1241359", "unmarked_context_8_1388_1241359", "Unmarked parent at depth 8, code 1388",
                "The frontier Boolean is false at remaining fuel 13, original node 1241359, the whole prefixCache at depth 8 and code 1388, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-22212-1239891", "node_context_10_22212_1239891", "Original split at fuel 11 and node 1239891",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1239619, 1239713, 1239831, 1239890. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-8-1388-1241359", "node_context_8_1388_1241359", "Original split at fuel 13 and node 1241359",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 1239568, 1240388, 1241149, 1241358. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-88851-1239890", "context_11_88851_1239890", "Context at depth 11, code 88851, node 1239890",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 88851 and original node 1239890, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-355589-34034", "context_12_355589_34034", "Context at depth 12, code 355589, node 34034",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 355589 and original node 34034, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
