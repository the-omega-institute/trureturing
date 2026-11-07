using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0055Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0055.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0055",
        H("Original frontier context coverage 0055"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-02644", "selected_cut_02644", "Selected cut at depth 13, code 22960, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 22960 returns the complete row with depth 13, base-four code 22960, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-02690", "selected_cut_02690", "Selected cut at depth 13, code 23012, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 23012 returns the complete row with depth 13, base-four code 23012, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-5739-82865", "unmarked_context_12_5739_82865", "Unmarked parent at depth 12, code 5739",
                "The frontier Boolean is false at remaining fuel 9, original node 82865, the whole prefixCache at depth 12 and code 5739, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-1437-83642", "unmarked_context_11_1437_83642", "Unmarked parent at depth 11, code 1437",
                "The frontier Boolean is false at remaining fuel 10, original node 83642, the whole prefixCache at depth 11 and code 1437, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-5739-82865", "node_context_12_5739_82865", "Original split at fuel 9 and node 82865",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 82817, 82851, 82864. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-1437-83642", "node_context_11_1437_83642", "Original split at fuel 10 and node 83642",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 83443, 83506, 83558, 83641. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-5739-82865", "context_12_5739_82865", "Context at depth 12, code 5739, node 82865",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 5739 and original node 82865, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_22956_3444, context_13_22957_82817, context_13_22958_82851, context_13_22959_82864.", DescribeRole.Theorem),
            Node("context-13-23012-3444", "context_13_23012_3444", "Context at depth 13, code 23012, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 23012 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
