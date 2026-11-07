using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1045Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1045.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1045",
        H("Original frontier context coverage 1045"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-50164", "selected_cut_50164", "Selected cut at depth 12, code 423502, node 1429445",
                "At remaining fuel 9 and original index 1429445, selection on the full partial prefix of depth 12 and code 423502 returns the complete row with depth 12, base-four code 423502, original node 1429445, kind 2, reserved field 0, 1433 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-50211", "selected_cut_50211", "Selected cut at depth 12, code 423981, node 1431472",
                "At remaining fuel 9 and original index 1431472, selection on the full partial prefix of depth 12 and code 423981 returns the complete row with depth 12, base-four code 423981, original node 1431472, kind 2, reserved field 0, 1969 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-105875-1429478", "unmarked_context_11_105875_1429478", "Unmarked parent at depth 11, code 105875",
                "The frontier Boolean is false at remaining fuel 10, original node 1429478, the whole prefixCache at depth 11 and code 105875, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-105992-1431307", "unmarked_context_11_105992_1431307", "Unmarked parent at depth 11, code 105992",
                "The frontier Boolean is false at remaining fuel 10, original node 1431307, the whole prefixCache at depth 11 and code 105992, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-105875-1429478", "node_context_11_105875_1429478", "Original split at fuel 10 and node 1429478",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1429409, 896706, 1429445, 1429477. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-105992-1431307", "node_context_11_105992_1431307", "Original split at fuel 10 and node 1431307",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 435160, 1431183, 1431242, 1431306. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-423502-1429445", "context_12_423502_1429445", "Context at depth 12, code 423502, node 1429445",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 423502 and original node 1429445, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-423981-1431472", "context_12_423981_1431472", "Context at depth 12, code 423981, node 1431472",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 423981 and original node 1431472, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
