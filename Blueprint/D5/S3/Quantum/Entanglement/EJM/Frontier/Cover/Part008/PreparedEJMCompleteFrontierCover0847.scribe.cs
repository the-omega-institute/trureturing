using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0847Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0847.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0847",
        H("Original frontier context coverage 0847"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 46 exact cut-selection equations, and 18 literal split equations paired with 18 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-40660", "selected_cut_40660", "Selected cut at depth 12, code 311107, node 1106715",
                "At remaining fuel 9 and original index 1106715, selection on the full partial prefix of depth 12 and code 311107 returns the complete row with depth 12, base-four code 311107, original node 1106715, kind 2, reserved field 0, 2301 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-40705", "selected_cut_40705", "Selected cut at depth 12, code 331801, node 1108376",
                "At remaining fuel 9 and original index 1108376, selection on the full partial prefix of depth 12 and code 331801 returns the complete row with depth 12, base-four code 331801, original node 1108376, kind 2, reserved field 0, 2245 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-77776-1106716", "unmarked_context_11_77776_1106716", "Unmarked parent at depth 11, code 77776",
                "The frontier Boolean is false at remaining fuel 10, original node 1106716, the whole prefixCache at depth 11 and code 77776, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-20736-1108173", "unmarked_context_10_20736_1108173", "Unmarked parent at depth 10, code 20736",
                "The frontier Boolean is false at remaining fuel 11, original node 1108173, the whole prefixCache at depth 10 and code 20736, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-77776-1106716", "node_context_11_77776_1106716", "Original split at fuel 10 and node 1106716",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1051681, 1106639, 1106678, 1106715. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-20736-1108173", "node_context_10_20736_1108173", "Original split at fuel 11 and node 1108173",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 434745, 1108069, 1108172, 1736. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-311107-1106715", "context_12_311107_1106715", "Context at depth 12, code 311107, node 1106715",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 311107 and original node 1106715, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-331801-1108376", "context_12_331801_1108376", "Context at depth 12, code 331801, node 1108376",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 331801 and original node 1108376, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
