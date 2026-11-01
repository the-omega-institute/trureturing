using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0816Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0816.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0816",
        H("Original frontier context coverage 0816"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-39171", "selected_cut_39171", "Selected cut at depth 12, code 302640, node 994572",
                "At remaining fuel 9 and original index 994572, selection on the full partial prefix of depth 12 and code 302640 returns the complete row with depth 12, base-four code 302640, original node 994572, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-39219", "selected_cut_39219", "Selected cut at depth 12, code 302706, node 1063517",
                "At remaining fuel 9 and original index 1063517, selection on the full partial prefix of depth 12 and code 302706 returns the complete row with depth 12, base-four code 302706, original node 1063517, kind 2, reserved field 0, 1649 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-75660-1061857", "unmarked_context_11_75660_1061857", "Unmarked parent at depth 11, code 75660",
                "The frontier Boolean is false at remaining fuel 10, original node 1061857, the whole prefixCache at depth 11 and code 75660, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-18918-1063426", "unmarked_context_10_18918_1063426", "Unmarked parent at depth 10, code 18918",
                "The frontier Boolean is false at remaining fuel 11, original node 1063426, the whole prefixCache at depth 10 and code 18918, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-75660-1061857", "node_context_11_75660_1061857", "Original split at fuel 10 and node 1061857",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 994572, 1061765, 1061808, 1061856. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-18918-1063426", "node_context_10_18918_1063426", "Original split at fuel 11 and node 1063426",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1063092, 1063171, 1063313, 1063425. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-302640-994572", "context_12_302640_994572", "Context at depth 12, code 302640, node 994572",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 302640 and original node 994572, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-302706-1063517", "context_12_302706_1063517", "Context at depth 12, code 302706, node 1063517",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 302706 and original node 1063517, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
