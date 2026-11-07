using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0446Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0446.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0446",
        H("Original frontier context coverage 0446"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-21411", "selected_cut_21411", "Selected cut at depth 13, code 300156, node 548118",
                "At remaining fuel 8 and original index 548118, selection on the full partial prefix of depth 13 and code 300156 returns the complete row with depth 13, base-four code 300156, original node 548118, kind 2, reserved field 0, 1733 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-21458", "selected_cut_21458", "Selected cut at depth 13, code 300209, node 549187",
                "At remaining fuel 8 and original index 549187, selection on the full partial prefix of depth 13 and code 300209 returns the complete row with depth 13, base-four code 300209, original node 549187, kind 2, reserved field 0, 3245 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-75039-548175", "unmarked_context_12_75039_548175", "Unmarked parent at depth 12, code 75039",
                "The frontier Boolean is false at remaining fuel 9, original node 548175, the whole prefixCache at depth 12 and code 75039, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-18762-549107", "unmarked_context_11_18762_549107", "Unmarked parent at depth 11, code 18762",
                "The frontier Boolean is false at remaining fuel 10, original node 549107, the whole prefixCache at depth 11 and code 18762, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-75039-548175", "node_context_12_75039_548175", "Original split at fuel 9 and node 548175",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 548118, 548145, 548168, 548174. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-18762-549107", "node_context_11_18762_549107", "Original split at fuel 10 and node 549107",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435790, 548945, 549018, 549106. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-300156-548118", "context_13_300156_548118", "Context at depth 13, code 300156, node 548118",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 300156 and original node 548118, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-300209-549187", "context_13_300209_549187", "Context at depth 13, code 300209, node 549187",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 300209 and original node 549187, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
