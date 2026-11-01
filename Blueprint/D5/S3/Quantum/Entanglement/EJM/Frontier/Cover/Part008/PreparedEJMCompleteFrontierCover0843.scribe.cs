using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0843Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0843.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0843",
        H("Original frontier context coverage 0843"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-40467", "selected_cut_40467", "Selected cut at depth 11, code 77424, node 1100728",
                "At remaining fuel 10 and original index 1100728, selection on the full partial prefix of depth 11 and code 77424 returns the complete row with depth 11, base-four code 77424, original node 1100728, kind 2, reserved field 0, 1949 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-40515", "selected_cut_40515", "Selected cut at depth 11, code 77514, node 900587",
                "At remaining fuel 10 and original index 900587, selection on the full partial prefix of depth 11 and code 77514 returns the complete row with depth 11, base-four code 77514, original node 900587, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-19356-1100899", "unmarked_context_10_19356_1100899", "Unmarked parent at depth 10, code 19356",
                "The frontier Boolean is false at remaining fuel 11, original node 1100899, the whole prefixCache at depth 10 and code 19356, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-77513-1102491", "unmarked_context_11_77513_1102491", "Unmarked parent at depth 11, code 77513",
                "The frontier Boolean is false at remaining fuel 10, original node 1102491, the whole prefixCache at depth 11 and code 77513, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-19356-1100899", "node_context_10_19356_1100899", "Original split at fuel 11 and node 1100899",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1100728, 1100775, 1100811, 1100898. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-77513-1102491", "node_context_11_77513_1102491", "Original split at fuel 10 and node 1102491",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1102355, 1102400, 1102446, 1102490. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-77424-1100728", "context_11_77424_1100728", "Context at depth 11, code 77424, node 1100728",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 77424 and original node 1100728, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-77514-900587", "context_11_77514_900587", "Context at depth 11, code 77514, node 900587",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 77514 and original node 900587, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
