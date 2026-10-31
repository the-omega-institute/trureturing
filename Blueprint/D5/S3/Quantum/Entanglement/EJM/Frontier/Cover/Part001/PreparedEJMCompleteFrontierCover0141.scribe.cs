using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0141Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0141.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0141",
        H("Original frontier context coverage 0141"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-06771", "selected_cut_06771", "Selected cut at depth 12, code 21900, node 200631",
                "At remaining fuel 9 and original index 200631, selection on the full partial prefix of depth 12 and code 21900 returns the complete row with depth 12, base-four code 21900, original node 200631, kind 2, reserved field 0, 1937 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-06818", "selected_cut_06818", "Selected cut at depth 13, code 88079, node 201819",
                "At remaining fuel 8 and original index 201819, selection on the full partial prefix of depth 13 and code 88079 returns the complete row with depth 13, base-four code 88079, original node 201819, kind 2, reserved field 0, 1125 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-5474-200597", "unmarked_context_11_5474_200597", "Unmarked parent at depth 11, code 5474",
                "The frontier Boolean is false at remaining fuel 10, original node 200597, the whole prefixCache at depth 11 and code 5474, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-13-88077-201783", "unmarked_context_13_88077_201783", "Unmarked parent at depth 13, code 88077",
                "The frontier Boolean is false at remaining fuel 8, original node 201783, the whole prefixCache at depth 13 and code 88077, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-5474-200597", "node_context_11_5474_200597", "Original split at fuel 10 and node 200597",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 200487, 200521, 200556, 200596. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-13-88077-201783", "node_context_13_88077_201783", "Original split at fuel 8 and node 201783",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 201736, 201756, 201770, 201782. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-5474-200597", "context_11_5474_200597", "Context at depth 11, code 5474, node 200597",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 5474 and original node 200597, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_21896_200487, context_12_21897_200521, context_12_21898_200556, context_12_21899_200596.", DescribeRole.Theorem),
            Node("context-13-88079-201819", "context_13_88079_201819", "Context at depth 13, code 88079, node 201819",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 88079 and original node 201819, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
