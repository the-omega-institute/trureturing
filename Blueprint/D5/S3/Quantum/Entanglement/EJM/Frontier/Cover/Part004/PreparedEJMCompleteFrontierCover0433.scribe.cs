using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0433Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0433.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0433",
        H("Original frontier context coverage 0433"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-20786", "selected_cut_20786", "Selected cut at depth 12, code 74516, node 435160",
                "At remaining fuel 9 and original index 435160, selection on the full partial prefix of depth 12 and code 74516 returns the complete row with depth 12, base-four code 74516, original node 435160, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-20834", "selected_cut_20834", "Selected cut at depth 13, code 298118, node 533189",
                "At remaining fuel 8 and original index 533189, selection on the full partial prefix of depth 13 and code 298118 returns the complete row with depth 13, base-four code 298118, original node 533189, kind 2, reserved field 0, 1169 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-74517-532162", "unmarked_context_12_74517_532162", "Unmarked parent at depth 12, code 74517",
                "The frontier Boolean is false at remaining fuel 9, original node 532162, the whole prefixCache at depth 12 and code 74517, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-4657-533105", "unmarked_context_10_4657_533105", "Unmarked parent at depth 10, code 4657",
                "The frontier Boolean is false at remaining fuel 11, original node 533105, the whole prefixCache at depth 10 and code 4657, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-74517-532162", "node_context_12_74517_532162", "Original split at fuel 9 and node 532162",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 532103, 532125, 532153, 532161. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-4657-533105", "node_context_10_4657_533105", "Original split at fuel 11 and node 533105",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 532056, 532363, 532742, 533104. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-74516-435160", "context_12_74516_435160", "Context at depth 12, code 74516, node 435160",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 74516 and original node 435160, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-298118-533189", "context_13_298118_533189", "Context at depth 13, code 298118, node 533189",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 298118 and original node 533189, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
