using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0910Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0910.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0910",
        H("Original frontier context coverage 0910"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-43683", "selected_cut_43683", "Selected cut at depth 12, code 352299, node 1197699",
                "At remaining fuel 9 and original index 1197699, selection on the full partial prefix of depth 12 and code 352299 returns the complete row with depth 12, base-four code 352299, original node 1197699, kind 2, reserved field 0, 2745 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-43730", "selected_cut_43730", "Selected cut at depth 12, code 352376, node 1199042",
                "At remaining fuel 9 and original index 1199042, selection on the full partial prefix of depth 12 and code 352376 returns the complete row with depth 12, base-four code 352376, original node 1199042, kind 2, reserved field 0, 1409 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-88074-1197700", "unmarked_context_11_88074_1197700", "Unmarked parent at depth 11, code 88074",
                "The frontier Boolean is false at remaining fuel 10, original node 1197700, the whole prefixCache at depth 11 and code 88074, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-88093-1199021", "unmarked_context_11_88093_1199021", "Unmarked parent at depth 11, code 88093",
                "The frontier Boolean is false at remaining fuel 10, original node 1199021, the whole prefixCache at depth 11 and code 88093, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-88074-1197700", "node_context_11_88074_1197700", "Original split at fuel 10 and node 1197700",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 101803, 1197641, 474208, 1197699. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-88093-1199021", "node_context_11_88093_1199021", "Original split at fuel 10 and node 1199021",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1198967, 896706, 1198991, 1199020. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-352299-1197699", "context_12_352299_1197699", "Context at depth 12, code 352299, node 1197699",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 352299 and original node 1197699, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-352376-1199042", "context_12_352376_1199042", "Context at depth 12, code 352376, node 1199042",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 352376 and original node 1199042, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
