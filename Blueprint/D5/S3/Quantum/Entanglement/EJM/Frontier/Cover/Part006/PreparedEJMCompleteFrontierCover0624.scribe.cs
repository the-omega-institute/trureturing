using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0624Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0624.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0624",
        H("Original frontier context coverage 0624"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-29956", "selected_cut_29956", "Selected cut at depth 13, code 375883, node 756643",
                "At remaining fuel 8 and original index 756643, selection on the full partial prefix of depth 13 and code 375883 returns the complete row with depth 13, base-four code 375883, original node 756643, kind 2, reserved field 0, 697 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-30004", "selected_cut_30004", "Selected cut at depth 13, code 375931, node 757805",
                "At remaining fuel 8 and original index 757805, selection on the full partial prefix of depth 13 and code 375931 returns the complete row with depth 13, base-four code 375931, original node 757805, kind 2, reserved field 0, 669 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-93970-756644", "unmarked_context_12_93970_756644", "Unmarked parent at depth 12, code 93970",
                "The frontier Boolean is false at remaining fuel 9, original node 756644, the whole prefixCache at depth 12 and code 93970, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-93981-757725", "unmarked_context_12_93981_757725", "Unmarked parent at depth 12, code 93981",
                "The frontier Boolean is false at remaining fuel 9, original node 757725, the whole prefixCache at depth 12 and code 93981, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-93970-756644", "node_context_12_93970_756644", "Original split at fuel 9 and node 756644",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 756568, 756603, 756635, 756643. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-93981-757725", "node_context_12_93981_757725", "Original split at fuel 9 and node 757725",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 757678, 757698, 757717, 757724. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-375883-756643", "context_13_375883_756643", "Context at depth 13, code 375883, node 756643",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 375883 and original node 756643, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-375931-757805", "context_13_375931_757805", "Context at depth 13, code 375931, node 757805",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 375931 and original node 757805, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
