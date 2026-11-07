using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0281Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0281.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0281",
        H("Original frontier context coverage 0281"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 50 exact cut-selection equations, and 14 literal split equations paired with 14 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-13490", "selected_cut_13490", "Selected cut at depth 13, code 106832, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 106832 returns the complete row with depth 13, base-four code 106832, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-13539", "selected_cut_13539", "Selected cut at depth 13, code 106926, node 354784",
                "At remaining fuel 8 and original index 354784, selection on the full partial prefix of depth 13 and code 106926 returns the complete row with depth 13, base-four code 106926, original node 354784, kind 2, reserved field 0, 2233 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26708-353791", "unmarked_context_12_26708_353791", "Unmarked parent at depth 12, code 26708",
                "The frontier Boolean is false at remaining fuel 9, original node 353791, the whole prefixCache at depth 12 and code 26708, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-26729-354745", "unmarked_context_12_26729_354745", "Unmarked parent at depth 12, code 26729",
                "The frontier Boolean is false at remaining fuel 9, original node 354745, the whole prefixCache at depth 12 and code 26729, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26708-353791", "node_context_12_26708_353791", "Original split at fuel 9 and node 353791",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 353757, 353778, 353790. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-26729-354745", "node_context_12_26729_354745", "Original split at fuel 9 and node 354745",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 354628, 354696, 354744. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-106832-3444", "context_13_106832_3444", "Context at depth 13, code 106832, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 106832 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-106926-354784", "context_13_106926_354784", "Context at depth 13, code 106926, node 354784",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 106926 and original node 354784, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
