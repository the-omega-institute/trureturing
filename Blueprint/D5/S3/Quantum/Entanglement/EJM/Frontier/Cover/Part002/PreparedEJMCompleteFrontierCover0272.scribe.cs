using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0272Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0272.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0272",
        H("Original frontier context coverage 0272"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-13059", "selected_cut_13059", "Selected cut at depth 12, code 26466, node 343617",
                "At remaining fuel 9 and original index 343617, selection on the full partial prefix of depth 12 and code 26466 returns the complete row with depth 12, base-four code 26466, original node 343617, kind 2, reserved field 0, 3989 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-13106", "selected_cut_13106", "Selected cut at depth 12, code 26495, node 345284",
                "At remaining fuel 9 and original index 345284, selection on the full partial prefix of depth 12 and code 26495 returns the complete row with depth 12, base-four code 26495, original node 345284, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-6616-343673", "unmarked_context_11_6616_343673", "Unmarked parent at depth 11, code 6616",
                "The frontier Boolean is false at remaining fuel 10, original node 343673, the whole prefixCache at depth 11 and code 6616, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-1655-345286", "unmarked_context_10_1655_345286", "Unmarked parent at depth 10, code 1655",
                "The frontier Boolean is false at remaining fuel 11, original node 345286, the whole prefixCache at depth 10 and code 1655, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-6616-343673", "node_context_11_6616_343673", "Original split at fuel 10 and node 343673",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 343431, 343550, 343617, 343672. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-1655-345286", "node_context_10_1655_345286", "Original split at fuel 11 and node 345286",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 344740, 344870, 345143, 345285. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-26466-343617", "context_12_26466_343617", "Context at depth 12, code 26466, node 343617",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 26466 and original node 343617, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-1655-345286", "context_10_1655_345286", "Context at depth 10, code 1655, node 345286",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 1655 and original node 345286, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_6620_344740, context_11_6621_344870, context_11_6622_345143, context_11_6623_345285.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
