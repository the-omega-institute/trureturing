using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0358Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0358.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0358",
        H("Original frontier context coverage 0358"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-17186", "selected_cut_17186", "Selected cut at depth 12, code 69719, node 893",
                "At remaining fuel 9 and original index 893, selection on the full partial prefix of depth 12 and code 69719 returns the complete row with depth 12, base-four code 69719, original node 893, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-17233", "selected_cut_17233", "Selected cut at depth 12, code 69895, node 893",
                "At remaining fuel 9 and original index 893, selection on the full partial prefix of depth 12 and code 69895 returns the complete row with depth 12, base-four code 69895, original node 893, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-17429-436956", "unmarked_context_11_17429_436956", "Unmarked parent at depth 11, code 17429",
                "The frontier Boolean is false at remaining fuel 10, original node 436956, the whole prefixCache at depth 11 and code 17429, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-69894-438508", "unmarked_context_12_69894_438508", "Unmarked parent at depth 12, code 69894",
                "The frontier Boolean is false at remaining fuel 9, original node 438508, the whole prefixCache at depth 12 and code 69894, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-17429-436956", "node_context_11_17429_436956", "Original split at fuel 10 and node 436956",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 895, 436890, 436955, 893. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-69894-438508", "node_context_12_69894_438508", "Original split at fuel 9 and node 438508",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 438403, 438463, 438489, 438507. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-69719-893", "context_12_69719_893", "Context at depth 12, code 69719, node 893",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 69719 and original node 893, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-69895-893", "context_12_69895_893", "Context at depth 12, code 69895, node 893",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 69895 and original node 893, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
