using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0484Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0484.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0484",
        H("Original frontier context coverage 0484"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-23235", "selected_cut_23235", "Selected cut at depth 13, code 305226, node 588063",
                "At remaining fuel 8 and original index 588063, selection on the full partial prefix of depth 13 and code 305226 returns the complete row with depth 13, base-four code 305226, original node 588063, kind 2, reserved field 0, 1245 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-23283", "selected_cut_23283", "Selected cut at depth 13, code 305277, node 589618",
                "At remaining fuel 8 and original index 589618, selection on the full partial prefix of depth 13 and code 305277 returns the complete row with depth 13, base-four code 305277, original node 589618, kind 2, reserved field 0, 2497 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-76306-588077", "unmarked_context_12_76306_588077", "Unmarked parent at depth 12, code 76306",
                "The frontier Boolean is false at remaining fuel 9, original node 588077, the whole prefixCache at depth 12 and code 76306, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-76318-589544", "unmarked_context_12_76318_589544", "Unmarked parent at depth 12, code 76318",
                "The frontier Boolean is false at remaining fuel 9, original node 589544, the whole prefixCache at depth 12 and code 76318, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-76306-588077", "node_context_12_76306_588077", "Original split at fuel 9 and node 588077",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 588018, 588042, 588063, 588076. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-76318-589544", "node_context_12_76318_589544", "Original split at fuel 9 and node 589544",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 589483, 589515, 589533, 589543. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-305226-588063", "context_13_305226_588063", "Context at depth 13, code 305226, node 588063",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 305226 and original node 588063, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-305277-589618", "context_13_305277_589618", "Context at depth 13, code 305277, node 589618",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 305277 and original node 589618, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
