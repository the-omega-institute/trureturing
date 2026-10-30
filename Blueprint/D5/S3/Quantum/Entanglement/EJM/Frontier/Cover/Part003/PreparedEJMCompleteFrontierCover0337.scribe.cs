using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0337Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0337.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0337",
        H("Original frontier context coverage 0337"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-16180", "selected_cut_16180", "Selected cut at depth 13, code 112699, node 412658",
                "At remaining fuel 8 and original index 412658, selection on the full partial prefix of depth 13 and code 112699 returns the complete row with depth 13, base-four code 112699, original node 412658, kind 2, reserved field 0, 1129 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-16227", "selected_cut_16227", "Selected cut at depth 13, code 112746, node 413822",
                "At remaining fuel 8 and original index 413822, selection on the full partial prefix of depth 13 and code 112746 returns the complete row with depth 13, base-four code 112746, original node 413822, kind 2, reserved field 0, 2081 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-28174-412659", "unmarked_context_12_28174_412659", "Unmarked parent at depth 12, code 28174",
                "The frontier Boolean is false at remaining fuel 9, original node 412659, the whole prefixCache at depth 12 and code 28174, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-28185-413691", "unmarked_context_12_28185_413691", "Unmarked parent at depth 12, code 28185",
                "The frontier Boolean is false at remaining fuel 9, original node 413691, the whole prefixCache at depth 12 and code 28185, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-28174-412659", "node_context_12_28174_412659", "Original split at fuel 9 and node 412659",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 412564, 412630, 412650, 412658. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-28185-413691", "node_context_12_28185_413691", "Original split at fuel 9 and node 413691",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 413633, 413663, 413680, 413690. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-112699-412658", "context_13_112699_412658", "Context at depth 13, code 112699, node 412658",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 112699 and original node 412658, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-112746-413822", "context_13_112746_413822", "Context at depth 13, code 112746, node 413822",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 112746 and original node 413822, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
