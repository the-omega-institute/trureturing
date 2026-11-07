using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0633Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0633.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0633",
        H("Original frontier context coverage 0633"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-30387", "selected_cut_30387", "Selected cut at depth 12, code 104502, node 767228",
                "At remaining fuel 9 and original index 767228, selection on the full partial prefix of depth 12 and code 104502 returns the complete row with depth 12, base-four code 104502, original node 767228, kind 2, reserved field 0, 3885 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-30434", "selected_cut_30434", "Selected cut at depth 12, code 104564, node 769616",
                "At remaining fuel 9 and original index 769616, selection on the full partial prefix of depth 12 and code 104564 returns the complete row with depth 12, base-four code 104564, original node 769616, kind 2, reserved field 0, 1697 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-104503-767341", "unmarked_context_12_104503_767341", "Unmarked parent at depth 12, code 104503",
                "The frontier Boolean is false at remaining fuel 9, original node 767341, the whole prefixCache at depth 12 and code 104503, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-26140-769576", "unmarked_context_11_26140_769576", "Unmarked parent at depth 11, code 26140",
                "The frontier Boolean is false at remaining fuel 10, original node 769576, the whole prefixCache at depth 11 and code 26140, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-104503-767341", "node_context_12_104503_767341", "Original split at fuel 9 and node 767341",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 767237, 767302, 767332, 767340. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-26140-769576", "node_context_11_26140_769576", "Original split at fuel 10 and node 769576",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 769468, 769507, 769536, 769575. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-104502-767228", "context_12_104502_767228", "Context at depth 12, code 104502, node 767228",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 104502 and original node 767228, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-104564-769616", "context_12_104564_769616", "Context at depth 12, code 104564, node 769616",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 104564 and original node 769616, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
