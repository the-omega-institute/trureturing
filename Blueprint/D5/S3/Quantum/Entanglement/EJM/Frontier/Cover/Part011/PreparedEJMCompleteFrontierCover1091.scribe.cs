using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1091Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1091.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1091",
        H("Original frontier context coverage 1091"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-52371", "selected_cut_52371", "Selected cut at depth 9, code 18081, node 1525743",
                "At remaining fuel 12 and original index 1525743, selection on the full partial prefix of depth 9 and code 18081 returns the complete row with depth 9, base-four code 18081, original node 1525743, kind 2, reserved field 0, 3981 subtree occurrences and completion domain 4194304. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-52418", "selected_cut_52418", "Selected cut at depth 10, code 72416, node 1468246",
                "At remaining fuel 11 and original index 1468246, selection on the full partial prefix of depth 10 and code 72416 returns the complete row with depth 10, base-four code 72416, original node 1468246, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-18080-1525531", "unmarked_context_9_18080_1525531", "Unmarked parent at depth 9, code 18080",
                "The frontier Boolean is false at remaining fuel 12, original node 1525531, the whole prefixCache at depth 9 and code 18080, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-8-4525-1528133", "unmarked_context_8_4525_1528133", "Unmarked parent at depth 8, code 4525",
                "The frontier Boolean is false at remaining fuel 13, original node 1528133, the whole prefixCache at depth 8 and code 4525, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-18080-1525531", "node_context_9_18080_1525531", "Original split at fuel 12 and node 1525531",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1468246, 1525310, 1525378, 1525530. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-8-4525-1528133", "node_context_8_4525_1528133", "Original split at fuel 13 and node 1528133",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 1527734, 1527979, 1528073, 1528132. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-9-18080-1525531", "context_9_18080_1525531", "Context at depth 9, code 18080, node 1525531",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 18080 and original node 1525531, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_72320_1468246, context_10_72321_1525310, context_10_72322_1525378, context_10_72323_1525530.", DescribeRole.Theorem),
            Node("context-10-72416-1468246", "context_10_72416_1468246", "Context at depth 10, code 72416, node 1468246",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 72416 and original node 1468246, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
