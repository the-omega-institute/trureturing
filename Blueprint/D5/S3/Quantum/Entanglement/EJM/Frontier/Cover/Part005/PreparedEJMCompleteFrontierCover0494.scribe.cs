using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0494Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0494.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0494",
        H("Original frontier context coverage 0494"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-23715", "selected_cut_23715", "Selected cut at depth 13, code 306441, node 599252",
                "At remaining fuel 8 and original index 599252, selection on the full partial prefix of depth 13 and code 306441 returns the complete row with depth 13, base-four code 306441, original node 599252, kind 2, reserved field 0, 2477 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-23762", "selected_cut_23762", "Selected cut at depth 13, code 306515, node 600201",
                "At remaining fuel 8 and original index 600201, selection on the full partial prefix of depth 13 and code 306515 returns the complete row with depth 13, base-four code 306515, original node 600201, kind 2, reserved field 0, 1049 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-76610-599279", "unmarked_context_12_76610_599279", "Unmarked parent at depth 12, code 76610",
                "The frontier Boolean is false at remaining fuel 9, original node 599279, the whole prefixCache at depth 12 and code 76610, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-76628-600202", "unmarked_context_12_76628_600202", "Unmarked parent at depth 12, code 76628",
                "The frontier Boolean is false at remaining fuel 9, original node 600202, the whole prefixCache at depth 12 and code 76628, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-76610-599279", "node_context_12_76610_599279", "Original split at fuel 9 and node 599279",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 599252, 599272, 599278. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-76628-600202", "node_context_12_76628_600202", "Original split at fuel 9 and node 600202",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 600165, 600188, 600201. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-306441-599252", "context_13_306441_599252", "Context at depth 13, code 306441, node 599252",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 306441 and original node 599252, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-76628-600202", "context_12_76628_600202", "Context at depth 12, code 76628, node 600202",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 76628 and original node 600202, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_306512_3444, context_13_306513_600165, context_13_306514_600188, context_13_306515_600201.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
