using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0159Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0159.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0159",
        H("Original frontier context coverage 0159"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-07634", "selected_cut_07634", "Selected cut at depth 13, code 90401, node 219974",
                "At remaining fuel 8 and original index 219974, selection on the full partial prefix of depth 13 and code 90401 returns the complete row with depth 13, base-four code 90401, original node 219974, kind 2, reserved field 0, 2353 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-07681", "selected_cut_07681", "Selected cut at depth 13, code 90451, node 220847",
                "At remaining fuel 8 and original index 220847, selection on the full partial prefix of depth 13 and code 90451 returns the complete row with depth 13, base-four code 90451, original node 220847, kind 2, reserved field 0, 1089 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-22600-220007", "unmarked_context_12_22600_220007", "Unmarked parent at depth 12, code 22600",
                "The frontier Boolean is false at remaining fuel 9, original node 220007, the whole prefixCache at depth 12 and code 22600, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-22612-220848", "unmarked_context_12_22612_220848", "Unmarked parent at depth 12, code 22612",
                "The frontier Boolean is false at remaining fuel 9, original node 220848, the whole prefixCache at depth 12 and code 22612, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-22600-220007", "node_context_12_22600_220007", "Original split at fuel 9 and node 220007",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 219974, 219994, 220006. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-22612-220848", "node_context_12_22612_220848", "Original split at fuel 9 and node 220848",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 220815, 220835, 220847. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-90401-219974", "context_13_90401_219974", "Context at depth 13, code 90401, node 219974",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 90401 and original node 219974, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-22612-220848", "context_12_22612_220848", "Context at depth 12, code 22612, node 220848",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 22612 and original node 220848, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_90448_3444, context_13_90449_220815, context_13_90450_220835, context_13_90451_220847.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
