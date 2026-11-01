using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0074Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0074.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0074",
        H("Original frontier context coverage 0074"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-03555", "selected_cut_03555", "Selected cut at depth 13, code 27981, node 111159",
                "At remaining fuel 8 and original index 111159, selection on the full partial prefix of depth 13 and code 27981 returns the complete row with depth 13, base-four code 27981, original node 111159, kind 2, reserved field 0, 2205 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-03602", "selected_cut_03602", "Selected cut at depth 12, code 7013, node 106538",
                "At remaining fuel 9 and original index 106538, selection on the full partial prefix of depth 12 and code 7013 returns the complete row with depth 12, base-four code 7013, original node 106538, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-6995-111194", "unmarked_context_12_6995_111194", "Unmarked parent at depth 12, code 6995",
                "The frontier Boolean is false at remaining fuel 9, original node 111194, the whole prefixCache at depth 12 and code 6995, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-1752-112179", "unmarked_context_11_1752_112179", "Unmarked parent at depth 11, code 1752",
                "The frontier Boolean is false at remaining fuel 10, original node 112179, the whole prefixCache at depth 11 and code 1752, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-6995-111194", "node_context_12_6995_111194", "Original split at fuel 9 and node 111194",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 111159, 111185, 111193. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-1752-112179", "node_context_11_1752_112179", "Original split at fuel 10 and node 112179",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 106538, 106538, 112103, 112178. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-27981-111159", "context_13_27981_111159", "Context at depth 13, code 27981, node 111159",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 27981 and original node 111159, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-7013-106538", "context_12_7013_106538", "Context at depth 12, code 7013, node 106538",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 7013 and original node 106538, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
