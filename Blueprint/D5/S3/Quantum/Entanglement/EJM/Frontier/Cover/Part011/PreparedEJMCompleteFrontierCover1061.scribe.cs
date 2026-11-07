using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1061Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1061.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1061",
        H("Original frontier context coverage 1061"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-50933", "selected_cut_50933", "Selected cut at depth 11, code 110495, node 977886",
                "At remaining fuel 10 and original index 977886, selection on the full partial prefix of depth 11 and code 110495 returns the complete row with depth 11, base-four code 110495, original node 977886, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-50979", "selected_cut_50979", "Selected cut at depth 12, code 456732, node 1461226",
                "At remaining fuel 9 and original index 1461226, selection on the full partial prefix of depth 12 and code 456732 returns the complete row with depth 12, base-four code 456732, original node 1461226, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-27623-1460773", "unmarked_context_10_27623_1460773", "Unmarked parent at depth 10, code 27623",
                "The frontier Boolean is false at remaining fuel 11, original node 1460773, the whole prefixCache at depth 10 and code 27623, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-114182-1462901", "unmarked_context_11_114182_1462901", "Unmarked parent at depth 11, code 114182",
                "The frontier Boolean is false at remaining fuel 10, original node 1462901, the whole prefixCache at depth 11 and code 114182, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-27623-1460773", "node_context_10_27623_1460773", "Original split at fuel 11 and node 1460773",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1460703, 1460745, 1460772, 977886. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-114182-1462901", "node_context_11_114182_1462901", "Original split at fuel 10 and node 1462901",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1461226, 1462824, 663554, 1462900. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-110495-977886", "context_11_110495_977886", "Context at depth 11, code 110495, node 977886",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 110495 and original node 977886, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-456732-1461226", "context_12_456732_1461226", "Context at depth 12, code 456732, node 1461226",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 456732 and original node 1461226, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
