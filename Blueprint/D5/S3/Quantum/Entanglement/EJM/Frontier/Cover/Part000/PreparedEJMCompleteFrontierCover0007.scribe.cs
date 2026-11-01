using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0007Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0007.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0007",
        H("Original frontier context coverage 0007"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-00338", "selected_cut_00338", "Selected cut at depth 13, code 5210, node 17454",
                "At remaining fuel 8 and original index 17454, selection on the full partial prefix of depth 13 and code 5210 returns the complete row with depth 13, base-four code 5210, original node 17454, kind 2, reserved field 0, 2749 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-00386", "selected_cut_00386", "Selected cut at depth 13, code 5306, node 18915",
                "At remaining fuel 8 and original index 18915, selection on the full partial prefix of depth 13 and code 5306 returns the complete row with depth 13, base-four code 5306, original node 18915, kind 2, reserved field 0, 1941 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-1302-17481", "unmarked_context_12_1302_17481", "Unmarked parent at depth 12, code 1302",
                "The frontier Boolean is false at remaining fuel 9, original node 17481, the whole prefixCache at depth 12 and code 1302, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-330-18788", "unmarked_context_11_330_18788", "Unmarked parent at depth 11, code 330",
                "The frontier Boolean is false at remaining fuel 10, original node 18788, the whole prefixCache at depth 11 and code 330, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-1302-17481", "node_context_12_1302_17481", "Original split at fuel 9 and node 17481",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 17358, 17413, 17454, 17480. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-330-18788", "node_context_11_330_18788", "Original split at fuel 10 and node 18788",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1738, 1738, 18654, 18787. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-5210-17454", "context_13_5210_17454", "Context at depth 13, code 5210, node 17454",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 5210 and original node 17454, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-5306-18915", "context_13_5306_18915", "Context at depth 13, code 5306, node 18915",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 5306 and original node 18915, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
