using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0398Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0398.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0398",
        H("Original frontier context coverage 0398"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-19107", "selected_cut_19107", "Selected cut at depth 13, code 288060, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 288060 returns the complete row with depth 13, base-four code 288060, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-19155", "selected_cut_19155", "Selected cut at depth 13, code 288111, node 490139",
                "At remaining fuel 8 and original index 490139, selection on the full partial prefix of depth 13 and code 288111 returns the complete row with depth 13, base-four code 288111, original node 490139, kind 2, reserved field 0, 1173 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-72015-489403", "unmarked_context_12_72015_489403", "Unmarked parent at depth 12, code 72015",
                "The frontier Boolean is false at remaining fuel 9, original node 489403, the whole prefixCache at depth 12 and code 72015, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-72026-490075", "unmarked_context_12_72026_490075", "Unmarked parent at depth 12, code 72026",
                "The frontier Boolean is false at remaining fuel 9, original node 490075, the whole prefixCache at depth 12 and code 72026, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-72015-489403", "node_context_12_72015_489403", "Original split at fuel 9 and node 489403",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 489369, 489396, 489402. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-72026-490075", "node_context_12_72026_490075", "Original split at fuel 9 and node 490075",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 490029, 490061, 490074. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-288060-3444", "context_13_288060_3444", "Context at depth 13, code 288060, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 288060 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-288111-490139", "context_13_288111_490139", "Context at depth 13, code 288111, node 490139",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 288111 and original node 490139, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
