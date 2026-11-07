using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0525Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0525.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0525",
        H("Original frontier context coverage 0525"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-25204", "selected_cut_25204", "Selected cut at depth 13, code 310636, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 310636 returns the complete row with depth 13, base-four code 310636, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-25251", "selected_cut_25251", "Selected cut at depth 12, code 77703, node 638386",
                "At remaining fuel 9 and original index 638386, selection on the full partial prefix of depth 12 and code 77703 returns the complete row with depth 12, base-four code 77703, original node 638386, kind 2, reserved field 0, 2497 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-77659-636511", "unmarked_context_12_77659_636511", "Unmarked parent at depth 12, code 77659",
                "The frontier Boolean is false at remaining fuel 9, original node 636511, the whole prefixCache at depth 12 and code 77659, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-19424-638245", "unmarked_context_11_19424_638245", "Unmarked parent at depth 11, code 19424",
                "The frontier Boolean is false at remaining fuel 10, original node 638245, the whole prefixCache at depth 11 and code 19424, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-77659-636511", "node_context_12_77659_636511", "Original split at fuel 9 and node 636511",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 636473, 636500, 636510. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-19424-638245", "node_context_11_19424_638245", "Original split at fuel 10 and node 638245",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 638148, 638188, 638217, 638244. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-310636-3444", "context_13_310636_3444", "Context at depth 13, code 310636, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 310636 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-77703-638386", "context_12_77703_638386", "Context at depth 12, code 77703, node 638386",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 77703 and original node 638386, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
