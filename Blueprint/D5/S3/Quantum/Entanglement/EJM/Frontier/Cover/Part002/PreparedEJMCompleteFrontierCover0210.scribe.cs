using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0210Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0210.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0210",
        H("Original frontier context coverage 0210"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-10083", "selected_cut_10083", "Selected cut at depth 13, code 99486, node 276340",
                "At remaining fuel 8 and original index 276340, selection on the full partial prefix of depth 13 and code 99486 returns the complete row with depth 13, base-four code 99486, original node 276340, kind 2, reserved field 0, 1441 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-10130", "selected_cut_10130", "Selected cut at depth 13, code 99533, node 277112",
                "At remaining fuel 8 and original index 277112, selection on the full partial prefix of depth 13 and code 99533 returns the complete row with depth 13, base-four code 99533, original node 277112, kind 2, reserved field 0, 2333 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-24871-276349", "unmarked_context_12_24871_276349", "Unmarked parent at depth 12, code 24871",
                "The frontier Boolean is false at remaining fuel 9, original node 276349, the whole prefixCache at depth 12 and code 24871, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-24882-277073", "unmarked_context_12_24882_277073", "Unmarked parent at depth 12, code 24882",
                "The frontier Boolean is false at remaining fuel 9, original node 277073, the whole prefixCache at depth 12 and code 24882, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-24871-276349", "node_context_12_24871_276349", "Original split at fuel 9 and node 276349",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 276296, 276322, 276340, 276348. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-24882-277073", "node_context_12_24882_277073", "Original split at fuel 9 and node 277073",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 277014, 277045, 277067, 277072. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-99486-276340", "context_13_99486_276340", "Context at depth 13, code 99486, node 276340",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 99486 and original node 276340, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-99533-277112", "context_13_99533_277112", "Context at depth 13, code 99533, node 277112",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 99533 and original node 277112, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
