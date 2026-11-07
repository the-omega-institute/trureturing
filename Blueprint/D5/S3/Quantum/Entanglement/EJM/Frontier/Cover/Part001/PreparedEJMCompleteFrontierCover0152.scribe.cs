using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0152Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0152.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0152",
        H("Original frontier context coverage 0152"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-07299", "selected_cut_07299", "Selected cut at depth 12, code 22200, node 212305",
                "At remaining fuel 9 and original index 212305, selection on the full partial prefix of depth 12 and code 22200 returns the complete row with depth 12, base-four code 22200, original node 212305, kind 2, reserved field 0, 1049 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-07345", "selected_cut_07345", "Selected cut at depth 13, code 90136, node 213695",
                "At remaining fuel 8 and original index 213695, selection on the full partial prefix of depth 13 and code 90136 returns the complete row with depth 13, base-four code 90136, original node 213695, kind 2, reserved field 0, 3837 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-5550-212345", "unmarked_context_11_5550_212345", "Unmarked parent at depth 11, code 5550",
                "The frontier Boolean is false at remaining fuel 10, original node 212345, the whole prefixCache at depth 11 and code 5550, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-22533-213636", "unmarked_context_12_22533_213636", "Unmarked parent at depth 12, code 22533",
                "The frontier Boolean is false at remaining fuel 9, original node 213636, the whole prefixCache at depth 12 and code 22533, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-5550-212345", "node_context_11_5550_212345", "Original split at fuel 10 and node 212345",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 212305, 212319, 212331, 212344. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-22533-213636", "node_context_12_22533_213636", "Original split at fuel 9 and node 213636",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 213538, 213598, 213623, 213635. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-22200-212305", "context_12_22200_212305", "Context at depth 12, code 22200, node 212305",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 22200 and original node 212305, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-90136-213695", "context_13_90136_213695", "Context at depth 13, code 90136, node 213695",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 90136 and original node 213695, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
