using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0034Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0034.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0034",
        H("Original frontier context coverage 0034"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-01634", "selected_cut_01634", "Selected cut at depth 13, code 18713, node 57520",
                "At remaining fuel 8 and original index 57520, selection on the full partial prefix of depth 13 and code 18713 returns the complete row with depth 13, base-four code 18713, original node 57520, kind 2, reserved field 0, 3341 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-01681", "selected_cut_01681", "Selected cut at depth 13, code 18763, node 58383",
                "At remaining fuel 8 and original index 58383, selection on the full partial prefix of depth 13 and code 18763 returns the complete row with depth 13, base-four code 18763, original node 58383, kind 2, reserved field 0, 1013 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-4678-57561", "unmarked_context_12_4678_57561", "Unmarked parent at depth 12, code 4678",
                "The frontier Boolean is false at remaining fuel 9, original node 57561, the whole prefixCache at depth 12 and code 4678, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-4690-58384", "unmarked_context_12_4690_58384", "Unmarked parent at depth 12, code 4690",
                "The frontier Boolean is false at remaining fuel 9, original node 58384, the whole prefixCache at depth 12 and code 4690, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-4678-57561", "node_context_12_4678_57561", "Original split at fuel 9 and node 57561",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 57520, 57546, 57560. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-4690-58384", "node_context_12_4690_58384", "Original split at fuel 9 and node 58384",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 58348, 58372, 58383. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-18713-57520", "context_13_18713_57520", "Context at depth 13, code 18713, node 57520",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 18713 and original node 57520, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-4690-58384", "context_12_4690_58384", "Context at depth 12, code 4690, node 58384",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 4690 and original node 58384, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_18760_3444, context_13_18761_58348, context_13_18762_58372, context_13_18763_58383.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
