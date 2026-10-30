using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0418Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0418.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0418",
        H("Original frontier context coverage 0418"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-20068", "selected_cut_20068", "Selected cut at depth 13, code 290095, node 513269",
                "At remaining fuel 8 and original index 513269, selection on the full partial prefix of depth 13 and code 290095 returns the complete row with depth 13, base-four code 290095, original node 513269, kind 2, reserved field 0, 865 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-20115", "selected_cut_20115", "Selected cut at depth 13, code 290169, node 514369",
                "At remaining fuel 8 and original index 514369, selection on the full partial prefix of depth 13 and code 290169 returns the complete row with depth 13, base-four code 290169, original node 514369, kind 2, reserved field 0, 1733 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-72523-513270", "unmarked_context_12_72523_513270", "Unmarked parent at depth 12, code 72523",
                "The frontier Boolean is false at remaining fuel 9, original node 513270, the whole prefixCache at depth 12 and code 72523, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-18134-514253", "unmarked_context_11_18134_514253", "Unmarked parent at depth 11, code 18134",
                "The frontier Boolean is false at remaining fuel 10, original node 514253, the whole prefixCache at depth 11 and code 18134, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-72523-513270", "node_context_12_72523_513270", "Original split at fuel 9 and node 513270",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 513236, 513256, 513269. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-18134-514253", "node_context_11_18134_514253", "Original split at fuel 10 and node 514253",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 514087, 514139, 514202, 514252. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-290095-513269", "context_13_290095_513269", "Context at depth 13, code 290095, node 513269",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 290095 and original node 513269, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-290169-514369", "context_13_290169_514369", "Context at depth 13, code 290169, node 514369",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 290169 and original node 514369, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
