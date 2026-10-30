using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1050Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1050.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1050",
        H("Original frontier context coverage 1050"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-50404", "selected_cut_50404", "Selected cut at depth 11, code 106195, node 1439347",
                "At remaining fuel 10 and original index 1439347, selection on the full partial prefix of depth 11 and code 106195 returns the complete row with depth 11, base-four code 106195, original node 1439347, kind 2, reserved field 0, 2593 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-50451", "selected_cut_50451", "Selected cut at depth 11, code 106254, node 1441330",
                "At remaining fuel 10 and original index 1441330, selection on the full partial prefix of depth 11 and code 106254 returns the complete row with depth 11, base-four code 106254, original node 1441330, kind 2, reserved field 0, 2889 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-26548-1439348", "unmarked_context_10_26548_1439348", "Unmarked parent at depth 10, code 26548",
                "The frontier Boolean is false at remaining fuel 11, original node 1439348, the whole prefixCache at depth 10 and code 26548, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-106252-1441177", "unmarked_context_11_106252_1441177", "Unmarked parent at depth 11, code 106252",
                "The frontier Boolean is false at remaining fuel 10, original node 1441177, the whole prefixCache at depth 11 and code 106252, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-26548-1439348", "node_context_10_26548_1439348", "Original split at fuel 11 and node 1439348",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1439148, 1439225, 1439290, 1439347. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-106252-1441177", "node_context_11_106252_1441177", "Original split at fuel 10 and node 1441177",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1416143, 1441097, 1441138, 1441176. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-106195-1439347", "context_11_106195_1439347", "Context at depth 11, code 106195, node 1439347",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 106195 and original node 1439347, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-106254-1441330", "context_11_106254_1441330", "Context at depth 11, code 106254, node 1441330",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 106254 and original node 1441330, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
