using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0447Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0447.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0447",
        H("Original frontier context coverage 0447"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-21459", "selected_cut_21459", "Selected cut at depth 13, code 300210, node 549243",
                "At remaining fuel 8 and original index 549243, selection on the full partial prefix of depth 13 and code 300210 returns the complete row with depth 13, base-four code 300210, original node 549243, kind 2, reserved field 0, 2525 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-21506", "selected_cut_21506", "Selected cut at depth 13, code 300260, node 550341",
                "At remaining fuel 8 and original index 550341, selection on the full partial prefix of depth 13 and code 300260 returns the complete row with depth 13, base-four code 300260, original node 550341, kind 2, reserved field 0, 329 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-75052-549258", "unmarked_context_12_75052_549258", "Unmarked parent at depth 12, code 75052",
                "The frontier Boolean is false at remaining fuel 9, original node 549258, the whole prefixCache at depth 12 and code 75052, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-75064-550332", "unmarked_context_12_75064_550332", "Unmarked parent at depth 12, code 75064",
                "The frontier Boolean is false at remaining fuel 9, original node 550332, the whole prefixCache at depth 12 and code 75064, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-75052-549258", "node_context_12_75052_549258", "Original split at fuel 9 and node 549258",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 549132, 549187, 549243, 549257. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-75064-550332", "node_context_12_75064_550332", "Original split at fuel 9 and node 550332",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 550158, 550229, 550294, 550331. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-300210-549243", "context_13_300210_549243", "Context at depth 13, code 300210, node 549243",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 300210 and original node 549243, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-300260-550341", "context_13_300260_550341", "Context at depth 13, code 300260, node 550341",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 300260 and original node 550341, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
