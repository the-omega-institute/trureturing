using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0729Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0729.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0729",
        H("Original frontier context coverage 0729"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-34995", "selected_cut_34995", "Selected cut at depth 12, code 283251, node 915655",
                "At remaining fuel 9 and original index 915655, selection on the full partial prefix of depth 12 and code 283251 returns the complete row with depth 12, base-four code 283251, original node 915655, kind 2, reserved field 0, 1633 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-35042", "selected_cut_35042", "Selected cut at depth 11, code 70835, node 916722",
                "At remaining fuel 10 and original index 916722, selection on the full partial prefix of depth 11 and code 70835 returns the complete row with depth 11, base-four code 70835, original node 916722, kind 2, reserved field 0, 2445 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-70812-915656", "unmarked_context_11_70812_915656", "Unmarked parent at depth 11, code 70812",
                "The frontier Boolean is false at remaining fuel 10, original node 915656, the whole prefixCache at depth 11 and code 70812, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-4426-916644", "unmarked_context_9_4426_916644", "Unmarked parent at depth 9, code 4426",
                "The frontier Boolean is false at remaining fuel 12, original node 916644, the whole prefixCache at depth 9 and code 4426, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-70812-915656", "node_context_11_70812_915656", "Original split at fuel 10 and node 915656",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 915615, 896706, 915630, 915655. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-4426-916644", "node_context_9_4426_916644", "Original split at fuel 12 and node 916644",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 916077, 916346, 916524, 916643. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-283251-915655", "context_12_283251_915655", "Context at depth 12, code 283251, node 915655",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 283251 and original node 915655, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-70835-916722", "context_11_70835_916722", "Context at depth 11, code 70835, node 916722",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 70835 and original node 916722, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
