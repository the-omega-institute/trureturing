using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1044Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1044.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1044",
        H("Original frontier context coverage 1044"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-50116", "selected_cut_50116", "Selected cut at depth 10, code 26452, node 793297",
                "At remaining fuel 11 and original index 793297, selection on the full partial prefix of depth 10 and code 26452 returns the complete row with depth 10, base-four code 26452, original node 793297, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-50163", "selected_cut_50163", "Selected cut at depth 12, code 423501, node 896706",
                "At remaining fuel 9 and original index 896706, selection on the full partial prefix of depth 12 and code 423501 returns the complete row with depth 12, base-four code 423501, original node 896706, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-26451-1427501", "unmarked_context_10_26451_1427501", "Unmarked parent at depth 10, code 26451",
                "The frontier Boolean is false at remaining fuel 11, original node 1427501, the whole prefixCache at depth 10 and code 26451, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-6616-1429231", "unmarked_context_9_6616_1429231", "Unmarked parent at depth 9, code 6616",
                "The frontier Boolean is false at remaining fuel 12, original node 1429231, the whole prefixCache at depth 9 and code 6616, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-26451-1427501", "node_context_10_26451_1427501", "Original split at fuel 11 and node 1427501",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1427186, 1427279, 1427463, 1427500. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-6616-1429231", "node_context_9_6616_1429231", "Original split at fuel 12 and node 1429231",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1428096, 1428484, 1428915, 1429230. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-26451-1427501", "context_10_26451_1427501", "Context at depth 10, code 26451, node 1427501",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 26451 and original node 1427501, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_105804_1427186, context_11_105805_1427279, context_11_105806_1427463, context_11_105807_1427500.", DescribeRole.Theorem),
            Node("context-12-423501-896706", "context_12_423501_896706", "Context at depth 12, code 423501, node 896706",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 423501 and original node 896706, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
