using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0779Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0779.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0779",
        H("Original frontier context coverage 0779"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-37395", "selected_cut_37395", "Selected cut at depth 13, code 1199127, node 999359",
                "At remaining fuel 8 and original index 999359, selection on the full partial prefix of depth 13 and code 1199127 returns the complete row with depth 13, base-four code 1199127, original node 999359, kind 2, reserved field 0, 509 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-37442", "selected_cut_37442", "Selected cut at depth 13, code 1199201, node 1000673",
                "At remaining fuel 8 and original index 1000673, selection on the full partial prefix of depth 13 and code 1199201 returns the complete row with depth 13, base-four code 1199201, original node 1000673, kind 2, reserved field 0, 1297 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-299781-999360", "unmarked_context_12_299781_999360", "Unmarked parent at depth 12, code 299781",
                "The frontier Boolean is false at remaining fuel 9, original node 999360, the whole prefixCache at depth 12 and code 299781, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-74949-1000623", "unmarked_context_11_74949_1000623", "Unmarked parent at depth 11, code 74949",
                "The frontier Boolean is false at remaining fuel 10, original node 1000623, the whole prefixCache at depth 11 and code 74949, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-299781-999360", "node_context_12_299781_999360", "Original split at fuel 9 and node 999360",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 999319, 999337, 999356, 999359. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-74949-1000623", "node_context_11_74949_1000623", "Original split at fuel 10 and node 1000623",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1000370, 1000516, 1000572, 1000622. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-1199127-999359", "context_13_1199127_999359", "Context at depth 13, code 1199127, node 999359",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1199127 and original node 999359, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-1199201-1000673", "context_13_1199201_1000673", "Context at depth 13, code 1199201, node 1000673",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1199201 and original node 1000673, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
