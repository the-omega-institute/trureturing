using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0897Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0897.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0897",
        H("Original frontier context coverage 0897"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-43059", "selected_cut_43059", "Selected cut at depth 12, code 339273, node 126371",
                "At remaining fuel 9 and original index 126371, selection on the full partial prefix of depth 12 and code 339273 returns the complete row with depth 12, base-four code 339273, original node 126371, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-43106", "selected_cut_43106", "Selected cut at depth 12, code 339347, node 1178237",
                "At remaining fuel 9 and original index 1178237, selection on the full partial prefix of depth 12 and code 339347 returns the complete row with depth 12, base-four code 339347, original node 1178237, kind 2, reserved field 0, 1193 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84818-1177315", "unmarked_context_11_84818_1177315", "Unmarked parent at depth 11, code 84818",
                "The frontier Boolean is false at remaining fuel 10, original node 1177315, the whole prefixCache at depth 11 and code 84818, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-84836-1178238", "unmarked_context_11_84836_1178238", "Unmarked parent at depth 11, code 84836",
                "The frontier Boolean is false at remaining fuel 10, original node 1178238, the whole prefixCache at depth 11 and code 84836, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84818-1177315", "node_context_11_84818_1177315", "Original split at fuel 10 and node 1177315",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1177247, 126371, 1177284, 1177314. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-84836-1178238", "node_context_11_84836_1178238", "Original split at fuel 10 and node 1178238",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1178177, 1178200, 1178219, 1178237. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-339273-126371", "context_12_339273_126371", "Context at depth 12, code 339273, node 126371",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 339273 and original node 126371, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-84836-1178238", "context_11_84836_1178238", "Context at depth 11, code 84836, node 1178238",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 84836 and original node 1178238, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_339344_1178177, context_12_339345_1178200, context_12_339346_1178219, context_12_339347_1178237.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
