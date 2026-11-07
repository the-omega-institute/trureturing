using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0274Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0274.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0274",
        H("Original frontier context coverage 0274"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-13155", "selected_cut_13155", "Selected cut at depth 12, code 26544, node 346801",
                "At remaining fuel 9 and original index 346801, selection on the full partial prefix of depth 12 and code 26544 returns the complete row with depth 12, base-four code 26544, original node 346801, kind 2, reserved field 0, 1361 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-13202", "selected_cut_13202", "Selected cut at depth 13, code 106526, node 348203",
                "At remaining fuel 8 and original index 348203, selection on the full partial prefix of depth 13 and code 106526 returns the complete row with depth 13, base-four code 106526, original node 348203, kind 2, reserved field 0, 2129 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-6636-346858", "unmarked_context_11_6636_346858", "Unmarked parent at depth 11, code 6636",
                "The frontier Boolean is false at remaining fuel 10, original node 346858, the whole prefixCache at depth 11 and code 6636, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-26630-348051", "unmarked_context_12_26630_348051", "Unmarked parent at depth 12, code 26630",
                "The frontier Boolean is false at remaining fuel 9, original node 348051, the whole prefixCache at depth 12 and code 26630, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-6636-346858", "node_context_11_6636_346858", "Original split at fuel 10 and node 346858",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 346801, 346827, 346844, 346857. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-26630-348051", "node_context_12_26630_348051", "Original split at fuel 9 and node 348051",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 347936, 348010, 348039, 348050. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-26544-346801", "context_12_26544_346801", "Context at depth 12, code 26544, node 346801",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 26544 and original node 346801, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-106526-348203", "context_13_106526_348203", "Context at depth 13, code 106526, node 348203",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 106526 and original node 348203, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
