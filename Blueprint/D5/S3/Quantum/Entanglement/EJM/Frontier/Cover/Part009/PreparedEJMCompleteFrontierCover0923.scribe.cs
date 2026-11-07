using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0923Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0923.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0923",
        H("Original frontier context coverage 0923"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-44307", "selected_cut_44307", "Selected cut at depth 12, code 353817, node 1218422",
                "At remaining fuel 9 and original index 1218422, selection on the full partial prefix of depth 12 and code 353817 returns the complete row with depth 12, base-four code 353817, original node 1218422, kind 2, reserved field 0, 2101 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-44354", "selected_cut_44354", "Selected cut at depth 12, code 353888, node 1219884",
                "At remaining fuel 9 and original index 1219884, selection on the full partial prefix of depth 12 and code 353888 returns the complete row with depth 12, base-four code 353888, original node 1219884, kind 2, reserved field 0, 1557 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-88454-1218482", "unmarked_context_11_88454_1218482", "Unmarked parent at depth 11, code 88454",
                "The frontier Boolean is false at remaining fuel 10, original node 1218482, the whole prefixCache at depth 11 and code 88454, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-22116-1219858", "unmarked_context_10_22116_1219858", "Unmarked parent at depth 10, code 22116",
                "The frontier Boolean is false at remaining fuel 11, original node 1219858, the whole prefixCache at depth 10 and code 22116, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-88454-1218482", "node_context_11_88454_1218482", "Original split at fuel 10 and node 1218482",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1218396, 1218422, 893903, 1218481. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-22116-1219858", "node_context_10_22116_1219858", "Original split at fuel 11 and node 1219858",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1219655, 1219717, 1219773, 1219857. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-353817-1218422", "context_12_353817_1218422", "Context at depth 12, code 353817, node 1218422",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 353817 and original node 1218422, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-353888-1219884", "context_12_353888_1219884", "Context at depth 12, code 353888, node 1219884",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 353888 and original node 1219884, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
