using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0366Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0366.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0366",
        H("Original frontier context coverage 0366"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-17571", "selected_cut_17571", "Selected cut at depth 12, code 70251, node 447731",
                "At remaining fuel 9 and original index 447731, selection on the full partial prefix of depth 12 and code 70251 returns the complete row with depth 12, base-four code 70251, original node 447731, kind 2, reserved field 0, 2645 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-17617", "selected_cut_17617", "Selected cut at depth 13, code 282664, node 449189",
                "At remaining fuel 8 and original index 449189, selection on the full partial prefix of depth 13 and code 282664 returns the complete row with depth 13, base-four code 282664, original node 449189, kind 2, reserved field 0, 2093 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-17562-447732", "unmarked_context_11_17562_447732", "Unmarked parent at depth 11, code 17562",
                "The frontier Boolean is false at remaining fuel 10, original node 447732, the whole prefixCache at depth 11 and code 17562, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-70665-449129", "unmarked_context_12_70665_449129", "Unmarked parent at depth 12, code 70665",
                "The frontier Boolean is false at remaining fuel 9, original node 449129, the whole prefixCache at depth 12 and code 70665, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-17562-447732", "node_context_11_17562_447732", "Original split at fuel 10 and node 447732",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 447654, 447693, 445248, 447731. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-70665-449129", "node_context_12_70665_449129", "Original split at fuel 9 and node 449129",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 449043, 449094, 449117, 449128. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-70251-447731", "context_12_70251_447731", "Context at depth 12, code 70251, node 447731",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 70251 and original node 447731, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-282664-449189", "context_13_282664_449189", "Context at depth 13, code 282664, node 449189",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 282664 and original node 449189, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
