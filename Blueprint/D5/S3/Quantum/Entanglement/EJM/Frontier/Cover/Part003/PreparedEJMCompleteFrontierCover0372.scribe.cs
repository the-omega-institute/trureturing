using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0372Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0372.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0372",
        H("Original frontier context coverage 0372"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-17858", "selected_cut_17858", "Selected cut at depth 13, code 283736, node 456066",
                "At remaining fuel 8 and original index 456066, selection on the full partial prefix of depth 13 and code 283736 returns the complete row with depth 13, base-four code 283736, original node 456066, kind 2, reserved field 0, 3905 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-17906", "selected_cut_17906", "Selected cut at depth 13, code 283811, node 458093",
                "At remaining fuel 8 and original index 458093, selection on the full partial prefix of depth 13 and code 283811 returns the complete row with depth 13, base-four code 283811, original node 458093, kind 2, reserved field 0, 1437 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-70934-456260", "unmarked_context_12_70934_456260", "Unmarked parent at depth 12, code 70934",
                "The frontier Boolean is false at remaining fuel 9, original node 456260, the whole prefixCache at depth 12 and code 70934, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-17737-457829", "unmarked_context_11_17737_457829", "Unmarked parent at depth 11, code 17737",
                "The frontier Boolean is false at remaining fuel 10, original node 457829, the whole prefixCache at depth 11 and code 17737, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-70934-456260", "node_context_12_70934_456260", "Original split at fuel 9 and node 456260",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 456066, 456130, 456192, 456259. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-17737-457829", "node_context_11_17737_457829", "Original split at fuel 10 and node 457829",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 455939, 455939, 457607, 457828. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-283736-456066", "context_13_283736_456066", "Context at depth 13, code 283736, node 456066",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 283736 and original node 456066, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-283811-458093", "context_13_283811_458093", "Context at depth 13, code 283811, node 458093",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 283811 and original node 458093, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
