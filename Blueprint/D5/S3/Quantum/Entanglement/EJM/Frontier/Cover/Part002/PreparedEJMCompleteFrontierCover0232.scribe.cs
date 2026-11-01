using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0232Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0232.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0232",
        H("Original frontier context coverage 0232"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-11139", "selected_cut_11139", "Selected cut at depth 12, code 25446, node 298732",
                "At remaining fuel 9 and original index 298732, selection on the full partial prefix of depth 12 and code 25446 returns the complete row with depth 12, base-four code 25446, original node 298732, kind 2, reserved field 0, 3661 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-11186", "selected_cut_11186", "Selected cut at depth 12, code 25478, node 300160",
                "At remaining fuel 9 and original index 300160, selection on the full partial prefix of depth 12 and code 25478 returns the complete row with depth 12, base-four code 25478, original node 300160, kind 2, reserved field 0, 2649 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-6361-298779", "unmarked_context_11_6361_298779", "Unmarked parent at depth 11, code 6361",
                "The frontier Boolean is false at remaining fuel 10, original node 298779, the whole prefixCache at depth 11 and code 6361, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-6368-300084", "unmarked_context_11_6368_300084", "Unmarked parent at depth 11, code 6368",
                "The frontier Boolean is false at remaining fuel 10, original node 300084, the whole prefixCache at depth 11 and code 6368, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-6361-298779", "node_context_11_6361_298779", "Original split at fuel 10 and node 298779",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 298619, 298689, 298732, 298778. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-6368-300084", "node_context_11_6368_300084", "Original split at fuel 10 and node 300084",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 299948, 299999, 300045, 300083. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-25446-298732", "context_12_25446_298732", "Context at depth 12, code 25446, node 298732",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25446 and original node 298732, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-25478-300160", "context_12_25478_300160", "Context at depth 12, code 25478, node 300160",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25478 and original node 300160, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
