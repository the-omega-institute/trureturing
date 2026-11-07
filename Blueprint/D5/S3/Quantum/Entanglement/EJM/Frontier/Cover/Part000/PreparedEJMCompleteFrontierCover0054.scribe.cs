using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0054Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0054.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0054",
        H("Original frontier context coverage 0054"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-02596", "selected_cut_02596", "Selected cut at depth 13, code 22912, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 22912 returns the complete row with depth 13, base-four code 22912, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-02643", "selected_cut_02643", "Selected cut at depth 13, code 22959, node 82864",
                "At remaining fuel 8 and original index 82864, selection on the full partial prefix of depth 13 and code 22959 returns the complete row with depth 13, base-four code 22959, original node 82864, kind 2, reserved field 0, 1105 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-5727-82052", "unmarked_context_12_5727_82052", "Unmarked parent at depth 12, code 5727",
                "The frontier Boolean is false at remaining fuel 9, original node 82052, the whole prefixCache at depth 12 and code 5727, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-5738-82804", "unmarked_context_12_5738_82804", "Unmarked parent at depth 12, code 5738",
                "The frontier Boolean is false at remaining fuel 9, original node 82804, the whole prefixCache at depth 12 and code 5738, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-5727-82052", "node_context_12_5727_82052", "Original split at fuel 9 and node 82052",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 82013, 82039, 82051. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-5738-82804", "node_context_12_5738_82804", "Original split at fuel 9 and node 82804",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 82704, 82766, 82803. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-5727-82052", "context_12_5727_82052", "Context at depth 12, code 5727, node 82052",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 5727 and original node 82052, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_13_22908_3444, context_13_22909_82013, context_13_22910_82039, context_13_22911_82051.", DescribeRole.Theorem),
            Node("context-13-22959-82864", "context_13_22959_82864", "Context at depth 13, code 22959, node 82864",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 22959 and original node 82864, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
