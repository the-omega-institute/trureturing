using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0356Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0356.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0356",
        H("Original frontier context coverage 0356"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 46 exact cut-selection equations, and 18 literal split equations paired with 18 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-17092", "selected_cut_17092", "Selected cut at depth 12, code 28600, node 434371",
                "At remaining fuel 9 and original index 434371, selection on the full partial prefix of depth 12 and code 28600 returns the complete row with depth 12, base-four code 28600, original node 434371, kind 2, reserved field 0, 1201 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-17137", "selected_cut_17137", "Selected cut at depth 13, code 278626, node 435575",
                "At remaining fuel 8 and original index 435575, selection on the full partial prefix of depth 13 and code 278626 returns the complete row with depth 13, base-four code 278626, original node 435575, kind 2, reserved field 0, 1849 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-7150-434409", "unmarked_context_11_7150_434409", "Unmarked parent at depth 11, code 7150",
                "The frontier Boolean is false at remaining fuel 10, original node 434409, the whole prefixCache at depth 11 and code 7150, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-17413-435482", "unmarked_context_11_17413_435482", "Unmarked parent at depth 11, code 17413",
                "The frontier Boolean is false at remaining fuel 10, original node 435482, the whole prefixCache at depth 11 and code 17413, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-7150-434409", "node_context_11_7150_434409", "Original split at fuel 10 and node 434409",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 434371, 434384, 434394, 434408. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-17413-435482", "node_context_11_17413_435482", "Original split at fuel 10 and node 435482",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435339, 435397, 435481, 893. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-28600-434371", "context_12_28600_434371", "Context at depth 12, code 28600, node 434371",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 28600 and original node 434371, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-278626-435575", "context_13_278626_435575", "Context at depth 13, code 278626, node 435575",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 278626 and original node 435575, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
