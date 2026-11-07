using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0212Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0212.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0212",
        H("Original frontier context coverage 0212"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-10180", "selected_cut_10180", "Selected cut at depth 13, code 99583, node 277899",
                "At remaining fuel 8 and original index 277899, selection on the full partial prefix of depth 13 and code 99583 returns the complete row with depth 13, base-four code 99583, original node 277899, kind 2, reserved field 0, 1041 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-10226", "selected_cut_10226", "Selected cut at depth 13, code 99644, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 99644 returns the complete row with depth 13, base-four code 99644, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-24895-277900", "unmarked_context_12_24895_277900", "Unmarked parent at depth 12, code 24895",
                "The frontier Boolean is false at remaining fuel 9, original node 277900, the whole prefixCache at depth 12 and code 24895, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-24910-278900", "unmarked_context_12_24910_278900", "Unmarked parent at depth 12, code 24910",
                "The frontier Boolean is false at remaining fuel 9, original node 278900, the whole prefixCache at depth 12 and code 24910, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-24895-277900", "node_context_12_24895_277900", "Original split at fuel 9 and node 277900",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 277847, 277871, 277891, 277899. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-24910-278900", "node_context_12_24910_278900", "Original split at fuel 9 and node 278900",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 278868, 278892, 278899. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-99583-277899", "context_13_99583_277899", "Context at depth 13, code 99583, node 277899",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 99583 and original node 277899, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-99644-3444", "context_13_99644_3444", "Context at depth 13, code 99644, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 99644 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
