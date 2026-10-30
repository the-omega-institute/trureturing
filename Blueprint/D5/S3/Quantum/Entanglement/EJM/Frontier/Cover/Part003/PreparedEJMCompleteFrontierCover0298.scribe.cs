using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0298Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0298.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0298",
        H("Original frontier context coverage 0298"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-14307", "selected_cut_14307", "Selected cut at depth 13, code 108696, node 370644",
                "At remaining fuel 8 and original index 370644, selection on the full partial prefix of depth 13 and code 108696 returns the complete row with depth 13, base-four code 108696, original node 370644, kind 2, reserved field 0, 897 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-14355", "selected_cut_14355", "Selected cut at depth 13, code 108747, node 371421",
                "At remaining fuel 8 and original index 371421, selection on the full partial prefix of depth 13 and code 108747 returns the complete row with depth 13, base-four code 108747, original node 371421, kind 2, reserved field 0, 877 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-27174-370684", "unmarked_context_12_27174_370684", "Unmarked parent at depth 12, code 27174",
                "The frontier Boolean is false at remaining fuel 9, original node 370684, the whole prefixCache at depth 12 and code 27174, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-27185-371366", "unmarked_context_12_27185_371366", "Unmarked parent at depth 12, code 27185",
                "The frontier Boolean is false at remaining fuel 9, original node 371366, the whole prefixCache at depth 12 and code 27185, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-27174-370684", "node_context_12_27174_370684", "Original split at fuel 9 and node 370684",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 370644, 370665, 370677, 370683. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-27185-371366", "node_context_12_27185_371366", "Original split at fuel 9 and node 371366",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 371316, 371345, 371360, 371365. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-108696-370644", "context_13_108696_370644", "Context at depth 13, code 108696, node 370644",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 108696 and original node 370644, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-108747-371421", "context_13_108747_371421", "Context at depth 13, code 108747, node 371421",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 108747 and original node 371421, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
