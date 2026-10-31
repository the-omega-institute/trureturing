using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0642Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0642.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0642",
        H("Original frontier context coverage 0642"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-30819", "selected_cut_30819", "Selected cut at depth 13, code 420936, node 783545",
                "At remaining fuel 8 and original index 783545, selection on the full partial prefix of depth 13 and code 420936 returns the complete row with depth 13, base-four code 420936, original node 783545, kind 2, reserved field 0, 2289 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-30867", "selected_cut_30867", "Selected cut at depth 13, code 420984, node 784626",
                "At remaining fuel 8 and original index 784626, selection on the full partial prefix of depth 13 and code 420984 returns the complete row with depth 13, base-four code 420984, original node 784626, kind 2, reserved field 0, 1369 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-105234-783608", "unmarked_context_12_105234_783608", "Unmarked parent at depth 12, code 105234",
                "The frontier Boolean is false at remaining fuel 9, original node 783608, the whole prefixCache at depth 12 and code 105234, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-105245-784605", "unmarked_context_12_105245_784605", "Unmarked parent at depth 12, code 105245",
                "The frontier Boolean is false at remaining fuel 9, original node 784605, the whole prefixCache at depth 12 and code 105245, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-105234-783608", "node_context_12_105234_783608", "Original split at fuel 9 and node 783608",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 783545, 783574, 783600, 783607. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-105245-784605", "node_context_12_105245_784605", "Original split at fuel 9 and node 784605",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 784532, 784560, 784593, 784604. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-420936-783545", "context_13_420936_783545", "Context at depth 13, code 420936, node 783545",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 420936 and original node 783545, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-420984-784626", "context_13_420984_784626", "Context at depth 13, code 420984, node 784626",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 420984 and original node 784626, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
