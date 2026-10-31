using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0062Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0062.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0062",
        H("Original frontier context coverage 0062"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-02979", "selected_cut_02979", "Selected cut at depth 14, code 106917, node 92536",
                "At remaining fuel 7 and original index 92536, selection on the full partial prefix of depth 14 and code 106917 returns the complete row with depth 14, base-four code 106917, original node 92536, kind 2, reserved field 0, 1301 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-03027", "selected_cut_03027", "Selected cut at depth 14, code 107190, node 94078",
                "At remaining fuel 7 and original index 94078, selection on the full partial prefix of depth 14 and code 107190 returns the complete row with depth 14, base-four code 107190, original node 94078, kind 2, reserved field 0, 1101 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-26729-92596", "unmarked_context_13_26729_92596", "Unmarked parent at depth 13, code 26729",
                "The frontier Boolean is false at remaining fuel 8, original node 92596, the whole prefixCache at depth 13 and code 26729, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-1673-93921", "unmarked_context_11_1673_93921", "Unmarked parent at depth 11, code 1673",
                "The frontier Boolean is false at remaining fuel 10, original node 93921, the whole prefixCache at depth 11 and code 1673, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-26729-92596", "node_context_13_26729_92596", "Original split at fuel 8 and node 92596",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 92497, 92536, 92571, 92595. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-1673-93921", "node_context_11_1673_93921", "Original split at fuel 10 and node 93921",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1738, 1738, 93788, 93920. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-14-106917-92536", "context_14_106917_92536", "Context at depth 14, code 106917, node 92536",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 106917 and original node 92536, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-14-107190-94078", "context_14_107190_94078", "Context at depth 14, code 107190, node 94078",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 107190 and original node 94078, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
