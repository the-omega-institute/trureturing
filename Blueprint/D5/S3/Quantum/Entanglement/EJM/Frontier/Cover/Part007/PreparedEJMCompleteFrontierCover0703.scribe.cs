using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0703Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0703.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0703",
        H("Original frontier context coverage 0703"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-33748", "selected_cut_33748", "Selected cut at depth 12, code 110440, node 868895",
                "At remaining fuel 9 and original index 868895, selection on the full partial prefix of depth 12 and code 110440 returns the complete row with depth 12, base-four code 110440, original node 868895, kind 2, reserved field 0, 3113 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-33795", "selected_cut_33795", "Selected cut at depth 11, code 27624, node 870351",
                "At remaining fuel 10 and original index 870351, selection on the full partial prefix of depth 11 and code 27624 returns the complete row with depth 11, base-four code 27624, original node 870351, kind 2, reserved field 0, 3925 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-27610-869026", "unmarked_context_11_27610_869026", "Unmarked parent at depth 11, code 27610",
                "The frontier Boolean is false at remaining fuel 10, original node 869026, the whole prefixCache at depth 11 and code 27610, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-6905-870296", "unmarked_context_10_6905_870296", "Unmarked parent at depth 10, code 6905",
                "The frontier Boolean is false at remaining fuel 11, original node 870296, the whole prefixCache at depth 10 and code 6905, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-27610-869026", "node_context_11_27610_869026", "Original split at fuel 10 and node 869026",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 868895, 868939, 868977, 869025. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-6905-870296", "node_context_10_6905_870296", "Original split at fuel 11 and node 870296",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 870080, 870172, 870253, 870295. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-110440-868895", "context_12_110440_868895", "Context at depth 12, code 110440, node 868895",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 110440 and original node 868895, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-27624-870351", "context_11_27624_870351", "Context at depth 11, code 27624, node 870351",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 27624 and original node 870351, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
