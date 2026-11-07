using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0636Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0636.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0636",
        H("Original frontier context coverage 0636"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-30532", "selected_cut_30532", "Selected cut at depth 13, code 418939, node 773633",
                "At remaining fuel 8 and original index 773633, selection on the full partial prefix of depth 13 and code 418939 returns the complete row with depth 13, base-four code 418939, original node 773633, kind 2, reserved field 0, 1049 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-30579", "selected_cut_30579", "Selected cut at depth 13, code 419022, node 775103",
                "At remaining fuel 8 and original index 775103, selection on the full partial prefix of depth 13 and code 419022 returns the complete row with depth 13, base-four code 419022, original node 775103, kind 2, reserved field 0, 1105 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-104734-773634", "unmarked_context_12_104734_773634", "Unmarked parent at depth 12, code 104734",
                "The frontier Boolean is false at remaining fuel 9, original node 773634, the whole prefixCache at depth 12 and code 104734, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-6546-774731", "unmarked_context_10_6546_774731", "Unmarked parent at depth 10, code 6546",
                "The frontier Boolean is false at remaining fuel 11, original node 774731, the whole prefixCache at depth 10 and code 6546, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-104734-773634", "node_context_12_104734_773634", "Original split at fuel 9 and node 773634",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 773519, 773565, 773602, 773633. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-6546-774731", "node_context_10_6546_774731", "Original split at fuel 11 and node 774731",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 774089, 774312, 766338, 774730. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-418939-773633", "context_13_418939_773633", "Context at depth 13, code 418939, node 773633",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 418939 and original node 773633, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-419022-775103", "context_13_419022_775103", "Context at depth 13, code 419022, node 775103",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 419022 and original node 775103, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
