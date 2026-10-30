using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0972Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0972.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0972",
        H("Original frontier context coverage 0972"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-46660", "selected_cut_46660", "Selected cut at depth 12, code 371239, node 1301895",
                "At remaining fuel 9 and original index 1301895, selection on the full partial prefix of depth 12 and code 371239 returns the complete row with depth 12, base-four code 371239, original node 1301895, kind 2, reserved field 0, 2673 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-46707", "selected_cut_46707", "Selected cut at depth 11, code 92838, node 1303332",
                "At remaining fuel 10 and original index 1303332, selection on the full partial prefix of depth 11 and code 92838 returns the complete row with depth 11, base-four code 92838, original node 1303332, kind 2, reserved field 0, 1801 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-92809-1301896", "unmarked_context_11_92809_1301896", "Unmarked parent at depth 11, code 92809",
                "The frontier Boolean is false at remaining fuel 10, original node 1301896, the whole prefixCache at depth 11 and code 92809, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-23208-1303276", "unmarked_context_10_23208_1303276", "Unmarked parent at depth 10, code 23208",
                "The frontier Boolean is false at remaining fuel 11, original node 1303276, the whole prefixCache at depth 10 and code 23208, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-92809-1301896", "node_context_11_92809_1301896", "Original split at fuel 10 and node 1301896",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 450498, 688903, 1301830, 1301895. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-23208-1303276", "node_context_10_23208_1303276", "Original split at fuel 11 and node 1303276",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1303167, 1303203, 1303244, 1303275. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-371239-1301895", "context_12_371239_1301895", "Context at depth 12, code 371239, node 1301895",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 371239 and original node 1301895, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-92838-1303332", "context_11_92838_1303332", "Context at depth 11, code 92838, node 1303332",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 92838 and original node 1303332, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
