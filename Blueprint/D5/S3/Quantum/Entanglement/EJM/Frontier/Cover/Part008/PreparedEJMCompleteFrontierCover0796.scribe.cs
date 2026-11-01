using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0796Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0796.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0796",
        H("Original frontier context coverage 0796"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-38210", "selected_cut_38210", "Selected cut at depth 12, code 301073, node 1028381",
                "At remaining fuel 9 and original index 1028381, selection on the full partial prefix of depth 12 and code 301073 returns the complete row with depth 12, base-four code 301073, original node 1028381, kind 2, reserved field 0, 2813 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-38257", "selected_cut_38257", "Selected cut at depth 12, code 301123, node 1030324",
                "At remaining fuel 9 and original index 1030324, selection on the full partial prefix of depth 12 and code 301123 returns the complete row with depth 12, base-four code 301123, original node 1030324, kind 2, reserved field 0, 1781 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-75268-1028471", "unmarked_context_11_75268_1028471", "Unmarked parent at depth 11, code 75268",
                "The frontier Boolean is false at remaining fuel 10, original node 1028471, the whole prefixCache at depth 11 and code 75268, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-75280-1030325", "unmarked_context_11_75280_1030325", "Unmarked parent at depth 11, code 75280",
                "The frontier Boolean is false at remaining fuel 10, original node 1030325, the whole prefixCache at depth 11 and code 75280, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-75268-1028471", "node_context_11_75268_1028471", "Original split at fuel 10 and node 1028471",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 985390, 1028381, 1028426, 1028470. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-75280-1030325", "node_context_11_75280_1030325", "Original split at fuel 10 and node 1030325",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1030245, 1030274, 1030300, 1030324. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-301073-1028381", "context_12_301073_1028381", "Context at depth 12, code 301073, node 1028381",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 301073 and original node 1028381, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-75280-1030325", "context_11_75280_1030325", "Context at depth 11, code 75280, node 1030325",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 75280 and original node 1030325, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_301120_1030245, context_12_301121_1030274, context_12_301122_1030300, context_12_301123_1030324.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
