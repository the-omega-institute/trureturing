using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0244Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0244.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0244",
        H("Original frontier context coverage 0244"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-11715", "selected_cut_11715", "Selected cut at depth 11, code 6456, node 313228",
                "At remaining fuel 10 and original index 313228, selection on the full partial prefix of depth 11 and code 6456 returns the complete row with depth 11, base-four code 6456, original node 313228, kind 2, reserved field 0, 1677 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-11761", "selected_cut_11761", "Selected cut at depth 13, code 103459, node 314727",
                "At remaining fuel 8 and original index 314727, selection on the full partial prefix of depth 13 and code 103459 returns the complete row with depth 13, base-four code 103459, original node 314727, kind 2, reserved field 0, 1289 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-1613-313208", "unmarked_context_10_1613_313208", "Unmarked parent at depth 10, code 1613",
                "The frontier Boolean is false at remaining fuel 11, original node 313208, the whole prefixCache at depth 10 and code 1613, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-25864-314728", "unmarked_context_12_25864_314728", "Unmarked parent at depth 12, code 25864",
                "The frontier Boolean is false at remaining fuel 9, original node 314728, the whole prefixCache at depth 12 and code 25864, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-1613-313208", "node_context_10_1613_313208", "Original split at fuel 11 and node 313208",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 313136, 313166, 313189, 313207. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-25864-314728", "node_context_12_25864_314728", "Original split at fuel 9 and node 314728",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 314589, 314664, 314710, 314727. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-1613-313208", "context_10_1613_313208", "Context at depth 10, code 1613, node 313208",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 1613 and original node 313208, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_6452_313136, context_11_6453_313166, context_11_6454_313189, context_11_6455_313207.", DescribeRole.Theorem),
            Node("context-12-25864-314728", "context_12_25864_314728", "Context at depth 12, code 25864, node 314728",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25864 and original node 314728, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_103456_314589, context_13_103457_314664, context_13_103458_314710, context_13_103459_314727.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
