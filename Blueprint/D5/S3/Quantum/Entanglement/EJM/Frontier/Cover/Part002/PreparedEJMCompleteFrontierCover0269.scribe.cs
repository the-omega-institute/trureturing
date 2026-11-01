using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0269Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0269.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0269",
        H("Original frontier context coverage 0269"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-12915", "selected_cut_12915", "Selected cut at depth 13, code 105684, node 340208",
                "At remaining fuel 8 and original index 340208, selection on the full partial prefix of depth 13 and code 105684 returns the complete row with depth 13, base-four code 105684, original node 340208, kind 2, reserved field 0, 373 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-12962", "selected_cut_12962", "Selected cut at depth 13, code 105737, node 341088",
                "At remaining fuel 8 and original index 341088, selection on the full partial prefix of depth 13 and code 105737 returns the complete row with depth 13, base-four code 105737, original node 341088, kind 2, reserved field 0, 3013 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26421-340261", "unmarked_context_12_26421_340261", "Unmarked parent at depth 12, code 26421",
                "The frontier Boolean is false at remaining fuel 9, original node 340261, the whole prefixCache at depth 12 and code 26421, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-26433-341042", "unmarked_context_12_26433_341042", "Unmarked parent at depth 12, code 26433",
                "The frontier Boolean is false at remaining fuel 9, original node 341042, the whole prefixCache at depth 12 and code 26433, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26421-340261", "node_context_12_26421_340261", "Original split at fuel 9 and node 340261",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 340208, 340236, 340256, 340260. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-26433-341042", "node_context_12_26433_341042", "Original split at fuel 9 and node 341042",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 340976, 341028, 341041. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-105684-340208", "context_13_105684_340208", "Context at depth 13, code 105684, node 340208",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 105684 and original node 340208, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-105737-341088", "context_13_105737_341088", "Context at depth 13, code 105737, node 341088",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 105737 and original node 341088, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
