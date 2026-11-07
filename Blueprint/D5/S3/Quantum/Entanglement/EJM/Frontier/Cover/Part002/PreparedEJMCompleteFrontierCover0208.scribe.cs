using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0208Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0208.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0208",
        H("Original frontier context coverage 0208"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-09987", "selected_cut_09987", "Selected cut at depth 13, code 99387, node 274566",
                "At remaining fuel 8 and original index 274566, selection on the full partial prefix of depth 13 and code 99387 returns the complete row with depth 13, base-four code 99387, original node 274566, kind 2, reserved field 0, 1137 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-10034", "selected_cut_10034", "Selected cut at depth 13, code 99437, node 275444",
                "At remaining fuel 8 and original index 275444, selection on the full partial prefix of depth 13 and code 99437 returns the complete row with depth 13, base-four code 99437, original node 275444, kind 2, reserved field 0, 2273 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-24846-274567", "unmarked_context_12_24846_274567", "Unmarked parent at depth 12, code 24846",
                "The frontier Boolean is false at remaining fuel 9, original node 274567, the whole prefixCache at depth 12 and code 24846, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-24858-275384", "unmarked_context_12_24858_275384", "Unmarked parent at depth 12, code 24858",
                "The frontier Boolean is false at remaining fuel 9, original node 275384, the whole prefixCache at depth 12 and code 24858, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-24846-274567", "node_context_12_24846_274567", "Original split at fuel 9 and node 274567",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 274484, 274529, 274555, 274566. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-24858-275384", "node_context_12_24858_275384", "Original split at fuel 9 and node 275384",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 275327, 275354, 275374, 275383. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-99387-274566", "context_13_99387_274566", "Context at depth 13, code 99387, node 274566",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 99387 and original node 274566, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-99437-275444", "context_13_99437_275444", "Context at depth 13, code 99437, node 275444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 99437 and original node 275444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
