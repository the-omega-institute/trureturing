using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0634Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0634.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0634",
        H("Original frontier context coverage 0634"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-30435", "selected_cut_30435", "Selected cut at depth 12, code 104565, node 769652",
                "At remaining fuel 9 and original index 769652, selection on the full partial prefix of depth 12 and code 104565 returns the complete row with depth 12, base-four code 104565, original node 769652, kind 2, reserved field 0, 1501 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-30482", "selected_cut_30482", "Selected cut at depth 13, code 418883, node 771830",
                "At remaining fuel 8 and original index 771830, selection on the full partial prefix of depth 13 and code 418883 returns the complete row with depth 13, base-four code 418883, original node 771830, kind 2, reserved field 0, 861 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-26141-769720", "unmarked_context_11_26141_769720", "Unmarked parent at depth 11, code 26141",
                "The frontier Boolean is false at remaining fuel 10, original node 769720, the whole prefixCache at depth 11 and code 26141, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-6544-771700", "unmarked_context_10_6544_771700", "Unmarked parent at depth 10, code 6544",
                "The frontier Boolean is false at remaining fuel 11, original node 771700, the whole prefixCache at depth 10 and code 6544, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-26141-769720", "node_context_11_26141_769720", "Original split at fuel 10 and node 769720",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 769616, 769652, 769685, 769719. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-6544-771700", "node_context_10_6544_771700", "Original split at fuel 11 and node 771700",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 434745, 771331, 764169, 771699. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-104565-769652", "context_12_104565_769652", "Context at depth 12, code 104565, node 769652",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 104565 and original node 769652, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-418883-771830", "context_13_418883_771830", "Context at depth 13, code 418883, node 771830",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 418883 and original node 771830, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
