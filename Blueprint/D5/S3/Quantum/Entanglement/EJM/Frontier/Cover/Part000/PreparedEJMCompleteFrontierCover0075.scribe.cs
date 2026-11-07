using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0075Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0075.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0075",
        H("Original frontier context coverage 0075"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-03603", "selected_cut_03603", "Selected cut at depth 13, code 28056, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 28056 returns the complete row with depth 13, base-four code 28056, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-03650", "selected_cut_03650", "Selected cut at depth 12, code 7049, node 113590",
                "At remaining fuel 9 and original index 113590, selection on the full partial prefix of depth 12 and code 7049 returns the complete row with depth 12, base-four code 7049, original node 113590, kind 2, reserved field 0, 3189 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-7014-112292", "unmarked_context_12_7014_112292", "Unmarked parent at depth 12, code 7014",
                "The frontier Boolean is false at remaining fuel 9, original node 112292, the whole prefixCache at depth 12 and code 7014, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-1761-113504", "unmarked_context_11_1761_113504", "Unmarked parent at depth 11, code 1761",
                "The frontier Boolean is false at remaining fuel 10, original node 113504, the whole prefixCache at depth 11 and code 1761, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-7014-112292", "node_context_12_7014_112292", "Original split at fuel 9 and node 112292",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 112213, 112267, 112291. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-1761-113504", "node_context_11_1761_113504", "Original split at fuel 10 and node 113504",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 113325, 113390, 113445, 113503. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-28056-3444", "context_13_28056_3444", "Context at depth 13, code 28056, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 28056 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-7049-113590", "context_12_7049_113590", "Context at depth 12, code 7049, node 113590",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 7049 and original node 113590, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
