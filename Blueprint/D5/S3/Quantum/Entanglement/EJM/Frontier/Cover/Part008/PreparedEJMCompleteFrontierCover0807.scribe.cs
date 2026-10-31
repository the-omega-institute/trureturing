using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0807Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0807.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0807",
        H("Original frontier context coverage 0807"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-38740", "selected_cut_38740", "Selected cut at depth 12, code 301945, node 1047101",
                "At remaining fuel 9 and original index 1047101, selection on the full partial prefix of depth 12 and code 301945 returns the complete row with depth 12, base-four code 301945, original node 1047101, kind 2, reserved field 0, 1821 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-38786", "selected_cut_38786", "Selected cut at depth 13, code 1208342, node 1048593",
                "At remaining fuel 8 and original index 1048593, selection on the full partial prefix of depth 13 and code 1208342 returns the complete row with depth 13, base-four code 1208342, original node 1048593, kind 2, reserved field 0, 1041 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-75486-1047148", "unmarked_context_11_75486_1047148", "Unmarked parent at depth 11, code 75486",
                "The frontier Boolean is false at remaining fuel 10, original node 1047148, the whole prefixCache at depth 11 and code 75486, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-75520-1048374", "unmarked_context_11_75520_1048374", "Unmarked parent at depth 11, code 75520",
                "The frontier Boolean is false at remaining fuel 10, original node 1048374, the whole prefixCache at depth 11 and code 75520, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-75486-1047148", "node_context_11_75486_1047148", "Original split at fuel 10 and node 1047148",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1047071, 1047101, 1047128, 1047147. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-75520-1048374", "node_context_11_75520_1048374", "Original split at fuel 10 and node 1048374",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 34034, 1048287, 1048372, 1048373. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-301945-1047101", "context_12_301945_1047101", "Context at depth 12, code 301945, node 1047101",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 301945 and original node 1047101, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-1208342-1048593", "context_13_1208342_1048593", "Context at depth 13, code 1208342, node 1048593",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1208342 and original node 1048593, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
