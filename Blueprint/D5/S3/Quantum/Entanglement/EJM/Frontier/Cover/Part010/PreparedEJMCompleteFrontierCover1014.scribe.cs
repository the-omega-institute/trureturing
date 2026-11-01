using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1014Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1014.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1014",
        H("Original frontier context coverage 1014"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-48675", "selected_cut_48675", "Selected cut at depth 11, code 100557, node 1367147",
                "At remaining fuel 10 and original index 1367147, selection on the full partial prefix of depth 11 and code 100557 returns the complete row with depth 11, base-four code 100557, original node 1367147, kind 2, reserved field 0, 2661 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-48723", "selected_cut_48723", "Selected cut at depth 12, code 402747, node 1369382",
                "At remaining fuel 9 and original index 1369382, selection on the full partial prefix of depth 12 and code 402747 returns the complete row with depth 12, base-four code 402747, original node 1369382, kind 2, reserved field 0, 1733 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-25139-1367212", "unmarked_context_10_25139_1367212", "Unmarked parent at depth 10, code 25139",
                "The frontier Boolean is false at remaining fuel 11, original node 1367212, the whole prefixCache at depth 10 and code 25139, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-100684-1369170", "unmarked_context_11_100684_1369170", "Unmarked parent at depth 11, code 100684",
                "The frontier Boolean is false at remaining fuel 10, original node 1369170, the whole prefixCache at depth 11 and code 100684, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-25139-1367212", "node_context_10_25139_1367212", "Original split at fuel 11 and node 1367212",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1367069, 1367147, 1367211, 612961. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-100684-1369170", "node_context_11_100684_1369170", "Original split at fuel 10 and node 1369170",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1369044, 1369102, 1369169. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-100557-1367147", "context_11_100557_1367147", "Context at depth 11, code 100557, node 1367147",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 100557 and original node 1367147, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-402747-1369382", "context_12_402747_1369382", "Context at depth 12, code 402747, node 1369382",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 402747 and original node 1369382, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
