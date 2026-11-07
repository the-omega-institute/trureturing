using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0728Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0728.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0728",
        H("Original frontier context coverage 0728"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-34947", "selected_cut_34947", "Selected cut at depth 12, code 283182, node 914333",
                "At remaining fuel 9 and original index 914333, selection on the full partial prefix of depth 12 and code 283182 returns the complete row with depth 12, base-four code 283182, original node 914333, kind 2, reserved field 0, 3865 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-34994", "selected_cut_34994", "Selected cut at depth 12, code 283250, node 915630",
                "At remaining fuel 9 and original index 915630, selection on the full partial prefix of depth 12 and code 283250 returns the complete row with depth 12, base-four code 283250, original node 915630, kind 2, reserved field 0, 1345 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-70795-914393", "unmarked_context_11_70795_914393", "Unmarked parent at depth 11, code 70795",
                "The frontier Boolean is false at remaining fuel 10, original node 914393, the whole prefixCache at depth 11 and code 70795, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-17702-915597", "unmarked_context_10_17702_915597", "Unmarked parent at depth 10, code 17702",
                "The frontier Boolean is false at remaining fuel 11, original node 915597, the whole prefixCache at depth 10 and code 17702, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-70795-914393", "node_context_11_70795_914393", "Original split at fuel 10 and node 914393",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 914189, 914255, 914333, 914392. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-17702-915597", "node_context_10_17702_915597", "Original split at fuel 11 and node 915597",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 915391, 915452, 915512, 915596. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-283182-914333", "context_12_283182_914333", "Context at depth 12, code 283182, node 914333",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 283182 and original node 914333, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-283250-915630", "context_12_283250_915630", "Context at depth 12, code 283250, node 915630",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 283250 and original node 915630, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
