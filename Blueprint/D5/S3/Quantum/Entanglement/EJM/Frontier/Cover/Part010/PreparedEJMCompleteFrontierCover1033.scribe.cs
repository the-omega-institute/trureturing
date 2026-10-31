using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1033Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1033.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1033",
        H("Original frontier context coverage 1033"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-49588", "selected_cut_49588", "Selected cut at depth 11, code 102046, node 1404226",
                "At remaining fuel 10 and original index 1404226, selection on the full partial prefix of depth 11 and code 102046 returns the complete row with depth 11, base-four code 102046, original node 1404226, kind 2, reserved field 0, 2089 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-49635", "selected_cut_49635", "Selected cut at depth 11, code 102093, node 1405604",
                "At remaining fuel 10 and original index 1405604, selection on the full partial prefix of depth 11 and code 102093 returns the complete row with depth 11, base-four code 102093, original node 1405604, kind 2, reserved field 0, 3281 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-25511-1404242", "unmarked_context_10_25511_1404242", "Unmarked parent at depth 10, code 25511",
                "The frontier Boolean is false at remaining fuel 11, original node 1404242, the whole prefixCache at depth 10 and code 25511, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-102092-1405541", "unmarked_context_11_102092_1405541", "Unmarked parent at depth 11, code 102092",
                "The frontier Boolean is false at remaining fuel 10, original node 1405541, the whole prefixCache at depth 11 and code 102092, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-25511-1404242", "node_context_10_25511_1404242", "Original split at fuel 11 and node 1404242",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1404117, 1404182, 1404226, 1404241. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-102092-1405541", "node_context_11_102092_1405541", "Original split at fuel 10 and node 1405541",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1405471, 1405511, 1405540. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-102046-1404226", "context_11_102046_1404226", "Context at depth 11, code 102046, node 1404226",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 102046 and original node 1404226, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-102093-1405604", "context_11_102093_1405604", "Context at depth 11, code 102093, node 1405604",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 102093 and original node 1405604, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
