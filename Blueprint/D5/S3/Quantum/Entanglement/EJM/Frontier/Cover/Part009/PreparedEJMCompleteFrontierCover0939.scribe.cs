using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0939Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0939.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0939",
        H("Original frontier context coverage 0939"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-45076", "selected_cut_45076", "Selected cut at depth 12, code 355852, node 448748",
                "At remaining fuel 9 and original index 448748, selection on the full partial prefix of depth 12 and code 355852 returns the complete row with depth 12, base-four code 355852, original node 448748, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-45123", "selected_cut_45123", "Selected cut at depth 12, code 355899, node 1246633",
                "At remaining fuel 9 and original index 1246633, selection on the full partial prefix of depth 12 and code 355899 returns the complete row with depth 12, base-four code 355899, original node 1246633, kind 2, reserved field 0, 2377 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-88962-1244915", "unmarked_context_11_88962_1244915", "Unmarked parent at depth 11, code 88962",
                "The frontier Boolean is false at remaining fuel 10, original node 1244915, the whole prefixCache at depth 11 and code 88962, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-88974-1246634", "unmarked_context_11_88974_1246634", "Unmarked parent at depth 11, code 88974",
                "The frontier Boolean is false at remaining fuel 10, original node 1246634, the whole prefixCache at depth 11 and code 88974, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-88962-1244915", "node_context_11_88962_1244915", "Original split at fuel 10 and node 1244915",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 1244824, 893903, 1244914. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-88974-1246634", "node_context_11_88974_1246634", "Original split at fuel 10 and node 1246634",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1246554, 1246590, 893903, 1246633. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-88962-1244915", "context_11_88962_1244915", "Context at depth 11, code 88962, node 1244915",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 88962 and original node 1244915, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_355848_448748, context_12_355849_1244824, context_12_355850_893903, context_12_355851_1244914.", DescribeRole.Theorem),
            Node("context-11-88974-1246634", "context_11_88974_1246634", "Context at depth 11, code 88974, node 1246634",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 88974 and original node 1246634, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_355896_1246554, context_12_355897_1246590, context_12_355898_893903, context_12_355899_1246633.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
