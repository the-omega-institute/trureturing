using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0330Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0330.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0330",
        H("Original frontier context coverage 0330"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-15844", "selected_cut_15844", "Selected cut at depth 13, code 111847, node 405136",
                "At remaining fuel 8 and original index 405136, selection on the full partial prefix of depth 13 and code 111847 returns the complete row with depth 13, base-four code 111847, original node 405136, kind 2, reserved field 0, 925 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-15890", "selected_cut_15890", "Selected cut at depth 13, code 111899, node 405982",
                "At remaining fuel 8 and original index 405982, selection on the full partial prefix of depth 13 and code 111899 returns the complete row with depth 13, base-four code 111899, original node 405982, kind 2, reserved field 0, 881 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-27961-405137", "unmarked_context_12_27961_405137", "Unmarked parent at depth 12, code 27961",
                "The frontier Boolean is false at remaining fuel 9, original node 405137, the whole prefixCache at depth 12 and code 27961, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-27974-405983", "unmarked_context_12_27974_405983", "Unmarked parent at depth 12, code 27974",
                "The frontier Boolean is false at remaining fuel 9, original node 405983, the whole prefixCache at depth 12 and code 27974, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-27961-405137", "node_context_12_27961_405137", "Original split at fuel 9 and node 405137",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 405087, 405110, 405130, 405136. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-27974-405983", "node_context_12_27974_405983", "Original split at fuel 9 and node 405983",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 405952, 405974, 405982. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-111847-405136", "context_13_111847_405136", "Context at depth 13, code 111847, node 405136",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 111847 and original node 405136, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-27974-405983", "context_12_27974_405983", "Context at depth 12, code 27974, node 405983",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 27974 and original node 405983, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_111896_3444, context_13_111897_405952, context_13_111898_405974, context_13_111899_405982.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
