using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0369Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0369.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0369",
        H("Original frontier context coverage 0369"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 50 exact cut-selection equations, and 14 literal split equations paired with 14 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-17713", "selected_cut_17713", "Selected cut at depth 12, code 70720, node 450982",
                "At remaining fuel 9 and original index 450982, selection on the full partial prefix of depth 12 and code 70720 returns the complete row with depth 12, base-four code 70720, original node 450982, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-17762", "selected_cut_17762", "Selected cut at depth 12, code 70766, node 452429",
                "At remaining fuel 9 and original index 452429, selection on the full partial prefix of depth 12 and code 70766 returns the complete row with depth 12, base-four code 70766, original node 452429, kind 2, reserved field 0, 3165 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-17680-451074", "unmarked_context_11_17680_451074", "Unmarked parent at depth 11, code 17680",
                "The frontier Boolean is false at remaining fuel 10, original node 451074, the whole prefixCache at depth 11 and code 17680, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-17690-452313", "unmarked_context_11_17690_452313", "Unmarked parent at depth 11, code 17690",
                "The frontier Boolean is false at remaining fuel 10, original node 452313, the whole prefixCache at depth 11 and code 17690, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-17680-451074", "node_context_11_17680_451074", "Original split at fuel 10 and node 451074",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 450982, 451021, 451073, 893. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-17690-452313", "node_context_11_17690_452313", "Original split at fuel 10 and node 452313",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 452188, 452231, 452274, 452312. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-70720-450982", "context_12_70720_450982", "Context at depth 12, code 70720, node 450982",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 70720 and original node 450982, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-70766-452429", "context_12_70766_452429", "Context at depth 12, code 70766, node 452429",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 70766 and original node 452429, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
