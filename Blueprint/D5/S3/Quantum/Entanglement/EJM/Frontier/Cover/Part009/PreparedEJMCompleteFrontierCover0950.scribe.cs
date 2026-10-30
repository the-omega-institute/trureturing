using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0950Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0950.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0950",
        H("Original frontier context coverage 0950"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-45604", "selected_cut_45604", "Selected cut at depth 11, code 92083, node 1266621",
                "At remaining fuel 10 and original index 1266621, selection on the full partial prefix of depth 11 and code 92083 returns the complete row with depth 11, base-four code 92083, original node 1266621, kind 2, reserved field 0, 1181 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-45650", "selected_cut_45650", "Selected cut at depth 12, code 368690, node 1268171",
                "At remaining fuel 9 and original index 1268171, selection on the full partial prefix of depth 12 and code 368690 returns the complete row with depth 12, base-four code 368690, original node 1268171, kind 2, reserved field 0, 1745 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-23020-1266622", "unmarked_context_10_23020_1266622", "Unmarked parent at depth 10, code 23020",
                "The frontier Boolean is false at remaining fuel 11, original node 1266622, the whole prefixCache at depth 10 and code 23020, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-23042-1268111", "unmarked_context_10_23042_1268111", "Unmarked parent at depth 10, code 23042",
                "The frontier Boolean is false at remaining fuel 11, original node 1268111, the whole prefixCache at depth 10 and code 23042, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-23020-1266622", "node_context_10_23020_1266622", "Original split at fuel 11 and node 1266622",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1266556, 1266588, 1266599, 1266621. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-23042-1268111", "node_context_10_23042_1268111", "Original split at fuel 11 and node 1268111",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1267568, 1267817, 1267912, 1268110. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-92083-1266621", "context_11_92083_1266621", "Context at depth 11, code 92083, node 1266621",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 92083 and original node 1266621, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-368690-1268171", "context_12_368690_1268171", "Context at depth 12, code 368690, node 1268171",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 368690 and original node 1268171, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
