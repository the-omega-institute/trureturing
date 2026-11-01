using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0218Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0218.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0218",
        H("Original frontier context coverage 0218"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-10467", "selected_cut_10467", "Selected cut at depth 13, code 100431, node 284552",
                "At remaining fuel 8 and original index 284552, selection on the full partial prefix of depth 13 and code 100431 returns the complete row with depth 13, base-four code 100431, original node 284552, kind 2, reserved field 0, 793 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-10515", "selected_cut_10515", "Selected cut at depth 13, code 100479, node 285463",
                "At remaining fuel 8 and original index 285463, selection on the full partial prefix of depth 13 and code 100479 returns the complete row with depth 13, base-four code 100479, original node 285463, kind 2, reserved field 0, 857 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-25107-284553", "unmarked_context_12_25107_284553", "Unmarked parent at depth 12, code 25107",
                "The frontier Boolean is false at remaining fuel 9, original node 284553, the whole prefixCache at depth 12 and code 25107, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-25118-285381", "unmarked_context_12_25118_285381", "Unmarked parent at depth 12, code 25118",
                "The frontier Boolean is false at remaining fuel 9, original node 285381, the whole prefixCache at depth 12 and code 25118, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-25107-284553", "node_context_12_25107_284553", "Original split at fuel 9 and node 284553",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 284501, 284528, 284545, 284552. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-25118-285381", "node_context_12_25118_285381", "Original split at fuel 9 and node 285381",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 285333, 285355, 285370, 285380. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-100431-284552", "context_13_100431_284552", "Context at depth 13, code 100431, node 284552",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 100431 and original node 284552, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-100479-285463", "context_13_100479_285463", "Context at depth 13, code 100479, node 285463",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 100479 and original node 285463, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
