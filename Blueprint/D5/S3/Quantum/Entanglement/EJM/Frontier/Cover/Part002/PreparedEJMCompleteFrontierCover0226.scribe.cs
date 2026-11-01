using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0226Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0226.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0226",
        H("Original frontier context coverage 0226"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-10851", "selected_cut_10851", "Selected cut at depth 13, code 101433, node 292885",
                "At remaining fuel 8 and original index 292885, selection on the full partial prefix of depth 13 and code 101433 returns the complete row with depth 13, base-four code 101433, original node 292885, kind 2, reserved field 0, 3333 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-10898", "selected_cut_10898", "Selected cut at depth 13, code 101474, node 293935",
                "At remaining fuel 8 and original index 293935, selection on the full partial prefix of depth 13 and code 101474 returns the complete row with depth 13, base-four code 101474, original node 293935, kind 2, reserved field 0, 1577 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-25358-292920", "unmarked_context_12_25358_292920", "Unmarked parent at depth 12, code 25358",
                "The frontier Boolean is false at remaining fuel 9, original node 292920, the whole prefixCache at depth 12 and code 25358, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-6341-293863", "unmarked_context_11_6341_293863", "Unmarked parent at depth 11, code 6341",
                "The frontier Boolean is false at remaining fuel 10, original node 293863, the whole prefixCache at depth 11 and code 6341, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-25358-292920", "node_context_12_25358_292920", "Original split at fuel 9 and node 292920",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 292837, 292885, 292911, 292919. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-6341-293863", "node_context_11_6341_293863", "Original split at fuel 10 and node 293863",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 293599, 293682, 293770, 293862. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-101433-292885", "context_13_101433_292885", "Context at depth 13, code 101433, node 292885",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 101433 and original node 292885, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-101474-293935", "context_13_101474_293935", "Context at depth 13, code 101474, node 293935",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 101474 and original node 293935, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
