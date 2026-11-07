using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0968Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0968.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0968",
        H("Original frontier context coverage 0968"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-46468", "selected_cut_46468", "Selected cut at depth 12, code 370744, node 994572",
                "At remaining fuel 9 and original index 994572, selection on the full partial prefix of depth 12 and code 370744 returns the complete row with depth 12, base-four code 370744, original node 994572, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-46515", "selected_cut_46515", "Selected cut at depth 11, code 92718, node 1297247",
                "At remaining fuel 10 and original index 1297247, selection on the full partial prefix of depth 11 and code 92718 returns the complete row with depth 11, base-four code 92718, original node 1297247, kind 2, reserved field 0, 1609 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-92685-1295895", "unmarked_context_11_92685_1295895", "Unmarked parent at depth 11, code 92685",
                "The frontier Boolean is false at remaining fuel 10, original node 1295895, the whole prefixCache at depth 11 and code 92685, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-23177-1297134", "unmarked_context_10_23177_1297134", "Unmarked parent at depth 10, code 23177",
                "The frontier Boolean is false at remaining fuel 11, original node 1297134, the whole prefixCache at depth 10 and code 23177, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-92685-1295895", "node_context_11_92685_1295895", "Original split at fuel 10 and node 1295895",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1295767, 1295803, 1295844, 1295894. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-23177-1297134", "node_context_10_23177_1297134", "Original split at fuel 11 and node 1297134",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1297061, 1192826, 1297098, 1297133. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-92685-1295895", "context_11_92685_1295895", "Context at depth 11, code 92685, node 1295895",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 92685 and original node 1295895, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_370740_1295767, context_12_370741_1295803, context_12_370742_1295844, context_12_370743_1295894.", DescribeRole.Theorem),
            Node("context-11-92718-1297247", "context_11_92718_1297247", "Context at depth 11, code 92718, node 1297247",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 92718 and original node 1297247, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
