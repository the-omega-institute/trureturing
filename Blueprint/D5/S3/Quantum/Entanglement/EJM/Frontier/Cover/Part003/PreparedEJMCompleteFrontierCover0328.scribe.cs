using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0328Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0328.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0328",
        H("Original frontier context coverage 0328"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-15747", "selected_cut_15747", "Selected cut at depth 13, code 111750, node 403269",
                "At remaining fuel 8 and original index 403269, selection on the full partial prefix of depth 13 and code 111750 returns the complete row with depth 13, base-four code 111750, original node 403269, kind 2, reserved field 0, 1809 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-15795", "selected_cut_15795", "Selected cut at depth 13, code 111798, node 404257",
                "At remaining fuel 8 and original index 404257, selection on the full partial prefix of depth 13 and code 111798 returns the complete row with depth 13, base-four code 111798, original node 404257, kind 2, reserved field 0, 1645 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-27937-403277", "unmarked_context_12_27937_403277", "Unmarked parent at depth 12, code 27937",
                "The frontier Boolean is false at remaining fuel 9, original node 403277, the whole prefixCache at depth 12 and code 27937, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-27948-404203", "unmarked_context_12_27948_404203", "Unmarked parent at depth 12, code 27948",
                "The frontier Boolean is false at remaining fuel 9, original node 404203, the whole prefixCache at depth 12 and code 27948, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-27937-403277", "node_context_12_27937_403277", "Original split at fuel 9 and node 403277",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 403224, 403247, 403269, 403276. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-27948-404203", "node_context_12_27948_404203", "Original split at fuel 9 and node 404203",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 404144, 404177, 404196, 404202. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-111750-403269", "context_13_111750_403269", "Context at depth 13, code 111750, node 403269",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 111750 and original node 403269, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-111798-404257", "context_13_111798_404257", "Context at depth 13, code 111798, node 404257",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 111798 and original node 404257, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
