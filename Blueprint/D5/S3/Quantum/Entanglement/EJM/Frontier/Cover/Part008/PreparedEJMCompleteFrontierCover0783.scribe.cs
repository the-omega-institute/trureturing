using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0783Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0783.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0783",
        H("Original frontier context coverage 0783"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-37587", "selected_cut_37587", "Selected cut at depth 13, code 1200186, node 1005766",
                "At remaining fuel 8 and original index 1005766, selection on the full partial prefix of depth 13 and code 1200186 returns the complete row with depth 13, base-four code 1200186, original node 1005766, kind 2, reserved field 0, 945 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-37634", "selected_cut_37634", "Selected cut at depth 12, code 300092, node 1007910",
                "At remaining fuel 9 and original index 1007910, selection on the full partial prefix of depth 12 and code 300092 returns the complete row with depth 12, base-four code 300092, original node 1007910, kind 2, reserved field 0, 2745 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-300046-1005775", "unmarked_context_12_300046_1005775", "Unmarked parent at depth 12, code 300046",
                "The frontier Boolean is false at remaining fuel 9, original node 1005775, the whole prefixCache at depth 12 and code 300046, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-75022-1007867", "unmarked_context_11_75022_1007867", "Unmarked parent at depth 11, code 75022",
                "The frontier Boolean is false at remaining fuel 10, original node 1007867, the whole prefixCache at depth 11 and code 75022, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-300046-1005775", "node_context_12_300046_1005775", "Original split at fuel 9 and node 1005775",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 1005717, 1005744, 1005766, 1005774. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-75022-1007867", "node_context_11_75022_1007867", "Original split at fuel 10 and node 1007867",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1007684, 1007736, 1007793, 1007866. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-1200186-1005766", "context_13_1200186_1005766", "Context at depth 13, code 1200186, node 1005766",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1200186 and original node 1005766, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-300092-1007910", "context_12_300092_1007910", "Context at depth 12, code 300092, node 1007910",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 300092 and original node 1007910, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
