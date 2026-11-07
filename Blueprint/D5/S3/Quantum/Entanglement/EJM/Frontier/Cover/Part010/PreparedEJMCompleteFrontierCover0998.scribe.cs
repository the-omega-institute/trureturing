using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0998Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0998.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0998",
        H("Original frontier context coverage 0998"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-47908", "selected_cut_47908", "Selected cut at depth 11, code 93658, node 1283737",
                "At remaining fuel 10 and original index 1283737, selection on the full partial prefix of depth 11 and code 93658 returns the complete row with depth 11, base-four code 93658, original node 1283737, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-47954", "selected_cut_47954", "Selected cut at depth 12, code 374819, node 1343268",
                "At remaining fuel 9 and original index 1343268, selection on the full partial prefix of depth 12 and code 374819 returns the complete row with depth 12, base-four code 374819, original node 1343268, kind 2, reserved field 0, 2001 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-23414-1341806", "unmarked_context_10_23414_1341806", "Unmarked parent at depth 10, code 23414",
                "The frontier Boolean is false at remaining fuel 11, original node 1341806, the whole prefixCache at depth 10 and code 23414, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-93704-1343269", "unmarked_context_11_93704_1343269", "Unmarked parent at depth 11, code 93704",
                "The frontier Boolean is false at remaining fuel 10, original node 1343269, the whole prefixCache at depth 11 and code 93704, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-23414-1341806", "node_context_10_23414_1341806", "Original split at fuel 11 and node 1341806",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1341700, 1341760, 1283737, 1341805. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-93704-1343269", "node_context_11_93704_1343269", "Original split at fuel 10 and node 1343269",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435790, 1343201, 1343237, 1343268. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-93658-1283737", "context_11_93658_1283737", "Context at depth 11, code 93658, node 1283737",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 93658 and original node 1283737, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-93704-1343269", "context_11_93704_1343269", "Context at depth 11, code 93704, node 1343269",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 93704 and original node 1343269, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_374816_435790, context_12_374817_1343201, context_12_374818_1343237, context_12_374819_1343268.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
