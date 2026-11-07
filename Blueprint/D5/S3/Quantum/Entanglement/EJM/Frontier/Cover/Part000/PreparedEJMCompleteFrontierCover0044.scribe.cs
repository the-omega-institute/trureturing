using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0044Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0044.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0044",
        H("Original frontier context coverage 0044"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-02114", "selected_cut_02114", "Selected cut at depth 12, code 5516, node 69664",
                "At remaining fuel 9 and original index 69664, selection on the full partial prefix of depth 12 and code 5516 returns the complete row with depth 12, base-four code 5516, original node 69664, kind 2, reserved field 0, 1673 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-02161", "selected_cut_02161", "Selected cut at depth 13, code 22546, node 71400",
                "At remaining fuel 8 and original index 71400, selection on the full partial prefix of depth 13 and code 22546 returns the complete row with depth 13, base-four code 22546, original node 71400, kind 2, reserved field 0, 3389 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-1379-69814", "unmarked_context_11_1379_69814", "Unmarked parent at depth 11, code 1379",
                "The frontier Boolean is false at remaining fuel 10, original node 69814, the whole prefixCache at depth 11 and code 1379, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-13-22545-71332", "unmarked_context_13_22545_71332", "Unmarked parent at depth 13, code 22545",
                "The frontier Boolean is false at remaining fuel 8, original node 71332, the whole prefixCache at depth 13 and code 22545, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-1379-69814", "node_context_11_1379_69814", "Original split at fuel 10 and node 69814",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 69664, 69723, 69774, 69813. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-13-22545-71332", "node_context_13_22545_71332", "Original split at fuel 8 and node 71332",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 71254, 71284, 71307, 71331. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-5516-69664", "context_12_5516_69664", "Context at depth 12, code 5516, node 69664",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 5516 and original node 69664, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-22546-71400", "context_13_22546_71400", "Context at depth 13, code 22546, node 71400",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 22546 and original node 71400, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
