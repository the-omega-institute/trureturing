using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1098Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1098.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1098",
        H("Original frontier context coverage 1098"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-52706", "selected_cut_52706", "Selected cut at depth 10, code 74801, node 1545688",
                "At remaining fuel 11 and original index 1545688, selection on the full partial prefix of depth 10 and code 74801 returns the complete row with depth 10, base-four code 74801, original node 1545688, kind 2, reserved field 0, 2417 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-52753", "selected_cut_52753", "Selected cut at depth 9, code 18880, node 1549163",
                "At remaining fuel 12 and original index 1549163, selection on the full partial prefix of depth 9 and code 18880 returns the complete row with depth 9, base-four code 18880, original node 1549163, kind 2, reserved field 0, 2653 subtree occurrences and completion domain 4194304. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-18700-1545887", "unmarked_context_9_18700_1545887", "Unmarked parent at depth 9, code 18700",
                "The frontier Boolean is false at remaining fuel 12, original node 1545887, the whole prefixCache at depth 9 and code 18700, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-6-292-1549011", "unmarked_context_6_292_1549011", "Unmarked parent at depth 6, code 292",
                "The frontier Boolean is false at remaining fuel 15, original node 1549011, the whole prefixCache at depth 6 and code 292, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-18700-1545887", "node_context_9_18700_1545887", "Original split at fuel 12 and node 1545887",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1468246, 1545688, 1545774, 1545886. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-6-292-1549011", "node_context_6_292_1549011", "Original split at fuel 15 and node 1549011",
                "The complete original decoder output is the split at coordinate 6, with value children 0 through 3 respectively at original indices 1546095, 1539247, 1547744, 1549010. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-74801-1545688", "context_10_74801_1545688", "Context at depth 10, code 74801, node 1545688",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 74801 and original node 1545688, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-9-18880-1549163", "context_9_18880_1549163", "Context at depth 9, code 18880, node 1549163",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 18880 and original node 1549163, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
