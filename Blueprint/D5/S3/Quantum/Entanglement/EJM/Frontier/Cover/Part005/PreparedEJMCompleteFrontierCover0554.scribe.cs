using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0554Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0554.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0554",
        H("Original frontier context coverage 0554"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-26596", "selected_cut_26596", "Selected cut at depth 13, code 355576, node 672432",
                "At remaining fuel 8 and original index 672432, selection on the full partial prefix of depth 13 and code 355576 returns the complete row with depth 13, base-four code 355576, original node 672432, kind 2, reserved field 0, 53 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-26643", "selected_cut_26643", "Selected cut at depth 13, code 355647, node 673378",
                "At remaining fuel 8 and original index 673378, selection on the full partial prefix of depth 13 and code 355647 returns the complete row with depth 13, base-four code 355647, original node 673378, kind 2, reserved field 0, 1093 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-88894-672484", "unmarked_context_12_88894_672484", "Unmarked parent at depth 12, code 88894",
                "The frontier Boolean is false at remaining fuel 9, original node 672484, the whole prefixCache at depth 12 and code 88894, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-88911-673379", "unmarked_context_12_88911_673379", "Unmarked parent at depth 12, code 88911",
                "The frontier Boolean is false at remaining fuel 9, original node 673379, the whole prefixCache at depth 12 and code 88911, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-88894-672484", "node_context_12_88894_672484", "Original split at fuel 9 and node 672484",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 672432, 672460, 672478, 672483. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-88911-673379", "node_context_12_88911_673379", "Original split at fuel 9 and node 673379",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 673343, 673369, 673378. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-355576-672432", "context_13_355576_672432", "Context at depth 13, code 355576, node 672432",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 355576 and original node 672432, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-88911-673379", "context_12_88911_673379", "Context at depth 12, code 88911, node 673379",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 88911 and original node 673379, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_355644_3444, context_13_355645_673343, context_13_355646_673369, context_13_355647_673378.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
