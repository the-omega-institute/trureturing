using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0715Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0715.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0715",
        H("Original frontier context coverage 0715"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-34324", "selected_cut_34324", "Selected cut at depth 13, code 452749, node 887426",
                "At remaining fuel 8 and original index 887426, selection on the full partial prefix of depth 13 and code 452749 returns the complete row with depth 13, base-four code 452749, original node 887426, kind 2, reserved field 0, 2261 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-34371", "selected_cut_34371", "Selected cut at depth 13, code 452820, node 888783",
                "At remaining fuel 8 and original index 888783, selection on the full partial prefix of depth 13 and code 452820 returns the complete row with depth 13, base-four code 452820, original node 888783, kind 2, reserved field 0, 733 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-113187-887452", "unmarked_context_12_113187_887452", "Unmarked parent at depth 12, code 113187",
                "The frontier Boolean is false at remaining fuel 9, original node 887452, the whole prefixCache at depth 12 and code 113187, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-113204-888765", "unmarked_context_12_113204_888765", "Unmarked parent at depth 12, code 113204",
                "The frontier Boolean is false at remaining fuel 9, original node 888765, the whole prefixCache at depth 12 and code 113204, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-113187-887452", "node_context_12_113187_887452", "Original split at fuel 9 and node 887452",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 887368, 887426, 887444, 887451. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-113204-888765", "node_context_12_113204_888765", "Original split at fuel 9 and node 888765",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 888677, 888740, 888759, 888764. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-452749-887426", "context_13_452749_887426", "Context at depth 13, code 452749, node 887426",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 452749 and original node 887426, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-452820-888783", "context_13_452820_888783", "Context at depth 13, code 452820, node 888783",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 452820 and original node 888783, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
