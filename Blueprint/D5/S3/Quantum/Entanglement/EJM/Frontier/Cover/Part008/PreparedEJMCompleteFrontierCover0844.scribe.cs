using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0844Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0844.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0844",
        H("Original frontier context coverage 0844"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-40516", "selected_cut_40516", "Selected cut at depth 12, code 310060, node 1102531",
                "At remaining fuel 9 and original index 1102531, selection on the full partial prefix of depth 12 and code 310060 returns the complete row with depth 12, base-four code 310060, original node 1102531, kind 2, reserved field 0, 2637 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-40564", "selected_cut_40564", "Selected cut at depth 12, code 310126, node 1104046",
                "At remaining fuel 9 and original index 1104046, selection on the full partial prefix of depth 12 and code 310126 returns the complete row with depth 12, base-four code 310126, original node 1104046, kind 2, reserved field 0, 1581 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-77515-1102606", "unmarked_context_11_77515_1102606", "Unmarked parent at depth 11, code 77515",
                "The frontier Boolean is false at remaining fuel 10, original node 1102606, the whole prefixCache at depth 11 and code 77515, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-77529-1103960", "unmarked_context_11_77529_1103960", "Unmarked parent at depth 11, code 77529",
                "The frontier Boolean is false at remaining fuel 10, original node 1103960, the whole prefixCache at depth 11 and code 77529, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-77515-1102606", "node_context_11_77515_1102606", "Original split at fuel 10 and node 1102606",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1102531, 1102571, 1102605, 903806. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-77529-1103960", "node_context_11_77529_1103960", "Original split at fuel 10 and node 1103960",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1103901, 1084018, 1103934, 1103959. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-310060-1102531", "context_12_310060_1102531", "Context at depth 12, code 310060, node 1102531",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 310060 and original node 1102531, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-310126-1104046", "context_12_310126_1104046", "Context at depth 12, code 310126, node 1104046",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 310126 and original node 1104046, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
