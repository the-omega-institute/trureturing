using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0822Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0822.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0822",
        H("Original frontier context coverage 0822"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 50 exact cut-selection equations, and 14 literal split equations paired with 14 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-39458", "selected_cut_39458", "Selected cut at depth 12, code 307220, node 26677",
                "At remaining fuel 9 and original index 26677, selection on the full partial prefix of depth 12 and code 307220 returns the complete row with depth 12, base-four code 307220, original node 26677, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-39507", "selected_cut_39507", "Selected cut at depth 12, code 307311, node 1071991",
                "At remaining fuel 9 and original index 1071991, selection on the full partial prefix of depth 12 and code 307311 returns the complete row with depth 12, base-four code 307311, original node 1071991, kind 2, reserved field 0, 1321 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-76805-1070770", "unmarked_context_11_76805_1070770", "Unmarked parent at depth 11, code 76805",
                "The frontier Boolean is false at remaining fuel 10, original node 1070770, the whole prefixCache at depth 11 and code 76805, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-76826-1071881", "unmarked_context_11_76826_1071881", "Unmarked parent at depth 11, code 76826",
                "The frontier Boolean is false at remaining fuel 10, original node 1071881, the whole prefixCache at depth 11 and code 76826, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-76805-1070770", "node_context_11_76805_1070770", "Original split at fuel 10 and node 1070770",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 26677, 124308, 1070733, 1070769. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-76826-1071881", "node_context_11_76826_1071881", "Original split at fuel 10 and node 1071881",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1071823, 1071849, 242157, 1071880. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-307220-26677", "context_12_307220_26677", "Context at depth 12, code 307220, node 26677",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 307220 and original node 26677, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-307311-1071991", "context_12_307311_1071991", "Context at depth 12, code 307311, node 1071991",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 307311 and original node 1071991, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
