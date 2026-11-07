using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0579Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0579.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0579",
        H("Original frontier context coverage 0579"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-27796", "selected_cut_27796", "Selected cut at depth 13, code 367663, node 702583",
                "At remaining fuel 8 and original index 702583, selection on the full partial prefix of depth 13 and code 367663 returns the complete row with depth 13, base-four code 367663, original node 702583, kind 2, reserved field 0, 769 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-27842", "selected_cut_27842", "Selected cut at depth 13, code 367715, node 703875",
                "At remaining fuel 8 and original index 703875, selection on the full partial prefix of depth 13 and code 367715 returns the complete row with depth 13, base-four code 367715, original node 703875, kind 2, reserved field 0, 729 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-91915-702584", "unmarked_context_12_91915_702584", "Unmarked parent at depth 12, code 91915",
                "The frontier Boolean is false at remaining fuel 9, original node 702584, the whole prefixCache at depth 12 and code 91915, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-91928-703876", "unmarked_context_12_91928_703876", "Unmarked parent at depth 12, code 91928",
                "The frontier Boolean is false at remaining fuel 9, original node 703876, the whole prefixCache at depth 12 and code 91928, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-91915-702584", "node_context_12_91915_702584", "Original split at fuel 9 and node 702584",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 702445, 702536, 702576, 702583. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-91928-703876", "node_context_12_91928_703876", "Original split at fuel 9 and node 703876",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 703817, 703847, 703866, 703875. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-367663-702583", "context_13_367663_702583", "Context at depth 13, code 367663, node 702583",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 367663 and original node 702583, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-91928-703876", "context_12_91928_703876", "Context at depth 12, code 91928, node 703876",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 91928 and original node 703876, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_367712_703817, context_13_367713_703847, context_13_367714_703866, context_13_367715_703875.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
