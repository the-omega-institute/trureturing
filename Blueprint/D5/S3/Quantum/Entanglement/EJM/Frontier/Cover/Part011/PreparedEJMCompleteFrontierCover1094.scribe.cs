using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1094Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1094.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1094",
        H("Original frontier context coverage 1094"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-52516", "selected_cut_52516", "Selected cut at depth 10, code 72547, node 1533698",
                "At remaining fuel 11 and original index 1533698, selection on the full partial prefix of depth 10 and code 72547 returns the complete row with depth 10, base-four code 72547, original node 1533698, kind 2, reserved field 0, 3401 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-52563", "selected_cut_52563", "Selected cut at depth 10, code 72627, node 1536389",
                "At remaining fuel 11 and original index 1536389, selection on the full partial prefix of depth 10 and code 72627 returns the complete row with depth 10, base-four code 72627, original node 1536389, kind 2, reserved field 0, 2005 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-72546-1533610", "unmarked_context_10_72546_1533610", "Unmarked parent at depth 10, code 72546",
                "The frontier Boolean is false at remaining fuel 11, original node 1533610, the whole prefixCache at depth 10 and code 72546, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-8-4538-1536057", "unmarked_context_8_4538_1536057", "Unmarked parent at depth 8, code 4538",
                "The frontier Boolean is false at remaining fuel 13, original node 1536057, the whole prefixCache at depth 8 and code 4538, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-72546-1533610", "node_context_10_72546_1533610", "Original split at fuel 11 and node 1533610",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1533558, 1533582, 1468743, 1533609. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-8-4538-1536057", "node_context_8_4538_1536057", "Original split at fuel 13 and node 1536057",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 1535720, 1535919, 1535996, 1536056. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-72546-1533610", "context_10_72546_1533610", "Context at depth 10, code 72546, node 1533610",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 72546 and original node 1533610, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_290184_1533558, context_11_290185_1533582, context_11_290186_1468743, context_11_290187_1533609.", DescribeRole.Theorem),
            Node("context-10-72627-1536389", "context_10_72627_1536389", "Context at depth 10, code 72627, node 1536389",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 72627 and original node 1536389, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
