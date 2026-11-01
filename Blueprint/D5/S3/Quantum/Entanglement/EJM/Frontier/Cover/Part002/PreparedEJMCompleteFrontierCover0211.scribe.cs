using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0211Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0211.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0211",
        H("Original frontier context coverage 0211"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-10131", "selected_cut_10131", "Selected cut at depth 13, code 99534, node 277131",
                "At remaining fuel 8 and original index 277131, selection on the full partial prefix of depth 13 and code 99534 returns the complete row with depth 13, base-four code 99534, original node 277131, kind 2, reserved field 0, 1665 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-10179", "selected_cut_10179", "Selected cut at depth 13, code 99582, node 277891",
                "At remaining fuel 8 and original index 277891, selection on the full partial prefix of depth 13 and code 99582 returns the complete row with depth 13, base-four code 99582, original node 277891, kind 2, reserved field 0, 1797 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-24883-277138", "unmarked_context_12_24883_277138", "Unmarked parent at depth 12, code 24883",
                "The frontier Boolean is false at remaining fuel 9, original node 277138, the whole prefixCache at depth 12 and code 24883, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-24894-277844", "unmarked_context_12_24894_277844", "Unmarked parent at depth 12, code 24894",
                "The frontier Boolean is false at remaining fuel 9, original node 277844, the whole prefixCache at depth 12 and code 24894, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-24883-277138", "node_context_12_24883_277138", "Original split at fuel 9 and node 277138",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 277083, 277112, 277131, 277137. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-24894-277844", "node_context_12_24894_277844", "Original split at fuel 9 and node 277844",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 277788, 277814, 277836, 277843. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-99534-277131", "context_13_99534_277131", "Context at depth 13, code 99534, node 277131",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 99534 and original node 277131, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-99582-277891", "context_13_99582_277891", "Context at depth 13, code 99582, node 277891",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 99582 and original node 277891, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
