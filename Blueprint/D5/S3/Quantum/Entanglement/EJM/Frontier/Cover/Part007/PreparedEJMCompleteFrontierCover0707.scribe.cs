using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0707Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0707.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0707",
        H("Original frontier context coverage 0707"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-33940", "selected_cut_33940", "Selected cut at depth 12, code 112699, node 875227",
                "At remaining fuel 9 and original index 875227, selection on the full partial prefix of depth 12 and code 112699 returns the complete row with depth 12, base-four code 112699, original node 875227, kind 2, reserved field 0, 3209 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-33986", "selected_cut_33986", "Selected cut at depth 9, code 1763, node 878223",
                "At remaining fuel 12 and original index 878223, selection on the full partial prefix of depth 9 and code 1763 returns the complete row with depth 9, base-four code 1763, original node 878223, kind 2, reserved field 0, 1069 subtree occurrences and completion domain 4194304. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-28174-875228", "unmarked_context_11_28174_875228", "Unmarked parent at depth 11, code 28174",
                "The frontier Boolean is false at remaining fuel 10, original node 875228, the whole prefixCache at depth 11 and code 28174, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-1762-878137", "unmarked_context_9_1762_878137", "Unmarked parent at depth 9, code 1762",
                "The frontier Boolean is false at remaining fuel 12, original node 878137, the whole prefixCache at depth 9 and code 1762, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-28174-875228", "node_context_11_28174_875228", "Original split at fuel 10 and node 875228",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 875022, 875105, 875157, 875227. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-1762-878137", "node_context_9_1762_878137", "Original split at fuel 12 and node 878137",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 875478, 878070, 878136, 875478. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-112699-875227", "context_12_112699_875227", "Context at depth 12, code 112699, node 875227",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 112699 and original node 875227, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-9-1763-878223", "context_9_1763_878223", "Context at depth 9, code 1763, node 878223",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 1763 and original node 878223, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
