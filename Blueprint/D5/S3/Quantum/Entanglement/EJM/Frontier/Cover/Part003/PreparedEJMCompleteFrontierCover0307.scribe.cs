using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0307Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0307.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0307",
        H("Original frontier context coverage 0307"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-14740", "selected_cut_14740", "Selected cut at depth 13, code 109675, node 380142",
                "At remaining fuel 8 and original index 380142, selection on the full partial prefix of depth 13 and code 109675 returns the complete row with depth 13, base-four code 109675, original node 380142, kind 2, reserved field 0, 773 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-14787", "selected_cut_14787", "Selected cut at depth 13, code 109722, node 381082",
                "At remaining fuel 8 and original index 381082, selection on the full partial prefix of depth 13 and code 109722 returns the complete row with depth 13, base-four code 109722, original node 381082, kind 2, reserved field 0, 1369 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-27418-380143", "unmarked_context_12_27418_380143", "Unmarked parent at depth 12, code 27418",
                "The frontier Boolean is false at remaining fuel 9, original node 380143, the whole prefixCache at depth 12 and code 27418, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-27429-381031", "unmarked_context_12_27429_381031", "Unmarked parent at depth 12, code 27429",
                "The frontier Boolean is false at remaining fuel 9, original node 381031, the whole prefixCache at depth 12 and code 27429, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-27418-380143", "node_context_12_27418_380143", "Original split at fuel 9 and node 380143",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 380090, 380118, 380137, 380142. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-27429-381031", "node_context_12_27429_381031", "Original split at fuel 9 and node 381031",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 380984, 381008, 381025, 381030. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-109675-380142", "context_13_109675_380142", "Context at depth 13, code 109675, node 380142",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 109675 and original node 380142, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-109722-381082", "context_13_109722_381082", "Context at depth 13, code 109722, node 381082",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 109722 and original node 381082, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
