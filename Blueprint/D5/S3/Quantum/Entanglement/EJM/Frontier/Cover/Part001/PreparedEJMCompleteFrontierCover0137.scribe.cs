using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0137Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0137.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0137",
        H("Original frontier context coverage 0137"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-06578", "selected_cut_06578", "Selected cut at depth 13, code 87074, node 196355",
                "At remaining fuel 8 and original index 196355, selection on the full partial prefix of depth 13 and code 87074 returns the complete row with depth 13, base-four code 87074, original node 196355, kind 2, reserved field 0, 2389 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-06625", "selected_cut_06625", "Selected cut at depth 13, code 87172, node 197474",
                "At remaining fuel 8 and original index 197474, selection on the full partial prefix of depth 13 and code 87172 returns the complete row with depth 13, base-four code 87172, original node 197474, kind 2, reserved field 0, 1181 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-21768-196372", "unmarked_context_12_21768_196372", "Unmarked parent at depth 12, code 21768",
                "The frontier Boolean is false at remaining fuel 9, original node 196372, the whole prefixCache at depth 12 and code 21768, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-21792-197457", "unmarked_context_12_21792_197457", "Unmarked parent at depth 12, code 21792",
                "The frontier Boolean is false at remaining fuel 9, original node 197457, the whole prefixCache at depth 12 and code 21792, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-21768-196372", "node_context_12_21768_196372", "Original split at fuel 9 and node 196372",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 196277, 196321, 196355, 196371. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-21792-197457", "node_context_12_21792_197457", "Original split at fuel 9 and node 197457",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 197408, 197428, 197448, 197456. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-87074-196355", "context_13_87074_196355", "Context at depth 13, code 87074, node 196355",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 87074 and original node 196355, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-87172-197474", "context_13_87172_197474", "Context at depth 13, code 87172, node 197474",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 87172 and original node 197474, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
