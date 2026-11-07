using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0238Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0238.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0238",
        H("Original frontier context coverage 0238"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-11427", "selected_cut_11427", "Selected cut at depth 13, code 102588, node 306029",
                "At remaining fuel 8 and original index 306029, selection on the full partial prefix of depth 13 and code 102588 returns the complete row with depth 13, base-four code 102588, original node 306029, kind 2, reserved field 0, 517 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-11474", "selected_cut_11474", "Selected cut at depth 13, code 102635, node 307009",
                "At remaining fuel 8 and original index 307009, selection on the full partial prefix of depth 13 and code 102635 returns the complete row with depth 13, base-four code 102635, original node 307009, kind 2, reserved field 0, 845 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-25647-306086", "unmarked_context_12_25647_306086", "Unmarked parent at depth 12, code 25647",
                "The frontier Boolean is false at remaining fuel 9, original node 306086, the whole prefixCache at depth 12 and code 25647, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-25658-307010", "unmarked_context_12_25658_307010", "Unmarked parent at depth 12, code 25658",
                "The frontier Boolean is false at remaining fuel 9, original node 307010, the whole prefixCache at depth 12 and code 25658, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-25647-306086", "node_context_12_25647_306086", "Original split at fuel 9 and node 306086",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 306029, 306059, 306078, 306085. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-25658-307010", "node_context_12_25658_307010", "Original split at fuel 9 and node 307010",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 306955, 306988, 307001, 307009. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-102588-306029", "context_13_102588_306029", "Context at depth 13, code 102588, node 306029",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 102588 and original node 306029, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-25658-307010", "context_12_25658_307010", "Context at depth 12, code 25658, node 307010",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 25658 and original node 307010, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_102632_306955, context_13_102633_306988, context_13_102634_307001, context_13_102635_307009.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
