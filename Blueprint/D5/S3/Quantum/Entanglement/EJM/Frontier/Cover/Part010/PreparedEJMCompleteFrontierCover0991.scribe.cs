using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0991Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0991.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0991",
        H("Original frontier context coverage 0991"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-47572", "selected_cut_47572", "Selected cut at depth 11, code 93415, node 1331832",
                "At remaining fuel 10 and original index 1331832, selection on the full partial prefix of depth 11 and code 93415 returns the complete row with depth 11, base-four code 93415, original node 1331832, kind 2, reserved field 0, 1277 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-47618", "selected_cut_47618", "Selected cut at depth 12, code 373811, node 1333200",
                "At remaining fuel 9 and original index 1333200, selection on the full partial prefix of depth 12 and code 373811 returns the complete row with depth 12, base-four code 373811, original node 1333200, kind 2, reserved field 0, 2293 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-23353-1331833", "unmarked_context_10_23353_1331833", "Unmarked parent at depth 10, code 23353",
                "The frontier Boolean is false at remaining fuel 11, original node 1331833, the whole prefixCache at depth 10 and code 23353, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-93452-1333201", "unmarked_context_11_93452_1333201", "Unmarked parent at depth 11, code 93452",
                "The frontier Boolean is false at remaining fuel 10, original node 1333201, the whole prefixCache at depth 11 and code 93452, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-23353-1331833", "node_context_10_23353_1331833", "Original split at fuel 11 and node 1331833",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1331742, 1331774, 1331811, 1331832. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-93452-1333201", "node_context_11_93452_1333201", "Original split at fuel 10 and node 1333201",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 985390, 1333115, 1333160, 1333200. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-93415-1331832", "context_11_93415_1331832", "Context at depth 11, code 93415, node 1331832",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 93415 and original node 1331832, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-93452-1333201", "context_11_93452_1333201", "Context at depth 11, code 93452, node 1333201",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 93452 and original node 1333201, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_373808_985390, context_12_373809_1333115, context_12_373810_1333160, context_12_373811_1333200.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
