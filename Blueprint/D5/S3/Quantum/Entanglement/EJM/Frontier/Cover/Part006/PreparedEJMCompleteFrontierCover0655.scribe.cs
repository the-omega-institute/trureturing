using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0655Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0655.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0655",
        H("Original frontier context coverage 0655"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-31444", "selected_cut_31444", "Selected cut at depth 13, code 424054, node 807307",
                "At remaining fuel 8 and original index 807307, selection on the full partial prefix of depth 13 and code 424054 returns the complete row with depth 13, base-four code 424054, original node 807307, kind 2, reserved field 0, 1553 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-31491", "selected_cut_31491", "Selected cut at depth 13, code 424101, node 808471",
                "At remaining fuel 8 and original index 808471, selection on the full partial prefix of depth 13 and code 424101 returns the complete row with depth 13, base-four code 424101, original node 808471, kind 2, reserved field 0, 2361 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-106013-807321", "unmarked_context_12_106013_807321", "Unmarked parent at depth 12, code 106013",
                "The frontier Boolean is false at remaining fuel 9, original node 807321, the whole prefixCache at depth 12 and code 106013, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-106024-808407", "unmarked_context_12_106024_808407", "Unmarked parent at depth 12, code 106024",
                "The frontier Boolean is false at remaining fuel 9, original node 808407, the whole prefixCache at depth 12 and code 106024, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-106013-807321", "node_context_12_106013_807321", "Original split at fuel 9 and node 807321",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 807239, 807281, 807307, 807320. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-106024-808407", "node_context_12_106024_808407", "Original split at fuel 9 and node 808407",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 808342, 808371, 808395, 808406. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-424054-807307", "context_13_424054_807307", "Context at depth 13, code 424054, node 807307",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 424054 and original node 807307, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-424101-808471", "context_13_424101_808471", "Context at depth 13, code 424101, node 808471",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 424101 and original node 808471, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
