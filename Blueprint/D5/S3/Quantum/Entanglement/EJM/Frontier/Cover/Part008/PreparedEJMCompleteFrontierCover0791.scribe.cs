using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0791Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0791.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0791",
        H("Original frontier context coverage 0791"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-37971", "selected_cut_37971", "Selected cut at depth 12, code 300648, node 1019893",
                "At remaining fuel 9 and original index 1019893, selection on the full partial prefix of depth 12 and code 300648 returns the complete row with depth 12, base-four code 300648, original node 1019893, kind 2, reserved field 0, 2553 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-38019", "selected_cut_38019", "Selected cut at depth 11, code 75183, node 1021529",
                "At remaining fuel 10 and original index 1021529, selection on the full partial prefix of depth 11 and code 75183 returns the complete row with depth 11, base-four code 75183, original node 1021529, kind 2, reserved field 0, 1713 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-75162-1019989", "unmarked_context_11_75162_1019989", "Unmarked parent at depth 11, code 75162",
                "The frontier Boolean is false at remaining fuel 10, original node 1019989, the whole prefixCache at depth 11 and code 75162, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-18794-1021375", "unmarked_context_10_18794_1021375", "Unmarked parent at depth 10, code 18794",
                "The frontier Boolean is false at remaining fuel 11, original node 1021375, the whole prefixCache at depth 10 and code 18794, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-75162-1019989", "node_context_11_75162_1019989", "Original split at fuel 10 and node 1019989",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1019893, 1019943, 661671, 1019988. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-18794-1021375", "node_context_10_18794_1021375", "Original split at fuel 11 and node 1021375",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1021299, 1021336, 906566, 1021374. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-300648-1019893", "context_12_300648_1019893", "Context at depth 12, code 300648, node 1019893",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 300648 and original node 1019893, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-75183-1021529", "context_11_75183_1021529", "Context at depth 11, code 75183, node 1021529",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 75183 and original node 1021529, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
