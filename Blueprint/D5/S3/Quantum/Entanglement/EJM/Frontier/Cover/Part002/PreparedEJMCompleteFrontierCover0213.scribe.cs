using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0213Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0213.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0213",
        H("Original frontier context coverage 0213"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-10227", "selected_cut_10227", "Selected cut at depth 13, code 99645, node 278919",
                "At remaining fuel 8 and original index 278919, selection on the full partial prefix of depth 13 and code 99645 returns the complete row with depth 13, base-four code 99645, original node 278919, kind 2, reserved field 0, 1705 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-10274", "selected_cut_10274", "Selected cut at depth 13, code 99740, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 99740 returns the complete row with depth 13, base-four code 99740, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-24911-278951", "unmarked_context_12_24911_278951", "Unmarked parent at depth 12, code 24911",
                "The frontier Boolean is false at remaining fuel 9, original node 278951, the whole prefixCache at depth 12 and code 24911, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-6232-279837", "unmarked_context_11_6232_279837", "Unmarked parent at depth 11, code 6232",
                "The frontier Boolean is false at remaining fuel 10, original node 279837, the whole prefixCache at depth 11 and code 6232, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-24911-278951", "node_context_12_24911_278951", "Original split at fuel 9 and node 278951",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 278919, 278942, 278950. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-6232-279837", "node_context_11_6232_279837", "Original split at fuel 10 and node 279837",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 279648, 279710, 279775, 279836. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-99645-278919", "context_13_99645_278919", "Context at depth 13, code 99645, node 278919",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 99645 and original node 278919, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-99740-3444", "context_13_99740_3444", "Context at depth 13, code 99740, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 99740 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
