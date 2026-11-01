using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0336Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0336.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0336",
        H("Original frontier context coverage 0336"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-16131", "selected_cut_16131", "Selected cut at depth 13, code 112650, node 410923",
                "At remaining fuel 8 and original index 410923, selection on the full partial prefix of depth 13 and code 112650 returns the complete row with depth 13, base-four code 112650, original node 410923, kind 2, reserved field 0, 557 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-16179", "selected_cut_16179", "Selected cut at depth 13, code 112698, node 412650",
                "At remaining fuel 8 and original index 412650, selection on the full partial prefix of depth 13 and code 112698 returns the complete row with depth 13, base-four code 112698, original node 412650, kind 2, reserved field 0, 1869 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-28162-410933", "unmarked_context_12_28162_410933", "Unmarked parent at depth 12, code 28162",
                "The frontier Boolean is false at remaining fuel 9, original node 410933, the whole prefixCache at depth 12 and code 28162, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-28173-412526", "unmarked_context_12_28173_412526", "Unmarked parent at depth 12, code 28173",
                "The frontier Boolean is false at remaining fuel 9, original node 412526, the whole prefixCache at depth 12 and code 28173, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-28162-410933", "node_context_12_28162_410933", "Original split at fuel 9 and node 410933",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 410838, 410903, 410923, 410932. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-28173-412526", "node_context_12_28173_412526", "Original split at fuel 9 and node 412526",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 412415, 412480, 412512, 412525. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-112650-410923", "context_13_112650_410923", "Context at depth 13, code 112650, node 410923",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 112650 and original node 410923, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-112698-412650", "context_13_112698_412650", "Context at depth 13, code 112698, node 412650",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 112698 and original node 412650, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
