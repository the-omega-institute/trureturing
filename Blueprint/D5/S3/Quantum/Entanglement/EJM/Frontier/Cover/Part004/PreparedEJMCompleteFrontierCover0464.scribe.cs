using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0464Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0464.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0464",
        H("Original frontier context coverage 0464"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-22276", "selected_cut_22276", "Selected cut at depth 13, code 302287, node 567383",
                "At remaining fuel 8 and original index 567383, selection on the full partial prefix of depth 13 and code 302287 returns the complete row with depth 13, base-four code 302287, original node 567383, kind 2, reserved field 0, 697 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-22322", "selected_cut_22322", "Selected cut at depth 13, code 302342, node 568273",
                "At remaining fuel 8 and original index 568273, selection on the full partial prefix of depth 13 and code 302342 returns the complete row with depth 13, base-four code 302342, original node 568273, kind 2, reserved field 0, 1405 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-75571-567384", "unmarked_context_12_75571_567384", "Unmarked parent at depth 12, code 75571",
                "The frontier Boolean is false at remaining fuel 9, original node 567384, the whole prefixCache at depth 12 and code 75571, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-75584-568204", "unmarked_context_12_75584_568204", "Unmarked parent at depth 12, code 75584",
                "The frontier Boolean is false at remaining fuel 9, original node 568204, the whole prefixCache at depth 12 and code 75584, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-75571-567384", "node_context_12_75571_567384", "Original split at fuel 9 and node 567384",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 567333, 567357, 567378, 567383. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-75584-568204", "node_context_12_75584_568204", "Original split at fuel 9 and node 568204",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 568178, 568196, 568203. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-302287-567383", "context_13_302287_567383", "Context at depth 13, code 302287, node 567383",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 302287 and original node 567383, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-302342-568273", "context_13_302342_568273", "Context at depth 13, code 302342, node 568273",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 302342 and original node 568273, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
