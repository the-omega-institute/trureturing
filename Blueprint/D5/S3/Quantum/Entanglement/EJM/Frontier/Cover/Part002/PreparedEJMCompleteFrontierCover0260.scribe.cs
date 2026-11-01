using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0260Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0260.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0260",
        H("Original frontier context coverage 0260"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-12482", "selected_cut_12482", "Selected cut at depth 13, code 104708, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 104708 returns the complete row with depth 13, base-four code 104708, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-12530", "selected_cut_12530", "Selected cut at depth 13, code 104759, node 330674",
                "At remaining fuel 8 and original index 330674, selection on the full partial prefix of depth 13 and code 104759 returns the complete row with depth 13, base-four code 104759, original node 330674, kind 2, reserved field 0, 1309 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26177-329763", "unmarked_context_12_26177_329763", "Unmarked parent at depth 12, code 26177",
                "The frontier Boolean is false at remaining fuel 9, original node 329763, the whole prefixCache at depth 12 and code 26177, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-26189-330675", "unmarked_context_12_26189_330675", "Unmarked parent at depth 12, code 26189",
                "The frontier Boolean is false at remaining fuel 9, original node 330675, the whole prefixCache at depth 12 and code 26189, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26177-329763", "node_context_12_26177_329763", "Original split at fuel 9 and node 329763",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 329718, 329752, 329762. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-26189-330675", "node_context_12_26189_330675", "Original split at fuel 9 and node 330675",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 330625, 330663, 330674. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-104708-3444", "context_13_104708_3444", "Context at depth 13, code 104708, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 104708 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-26189-330675", "context_12_26189_330675", "Context at depth 12, code 26189, node 330675",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 26189 and original node 330675, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_104756_3444, context_13_104757_330625, context_13_104758_330663, context_13_104759_330674.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
