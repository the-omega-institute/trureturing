using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0644Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0644.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0644",
        H("Original frontier context coverage 0644"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-30916", "selected_cut_30916", "Selected cut at depth 12, code 105271, node 786221",
                "At remaining fuel 9 and original index 786221, selection on the full partial prefix of depth 12 and code 105271 returns the complete row with depth 12, base-four code 105271, original node 786221, kind 2, reserved field 0, 3489 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-30963", "selected_cut_30963", "Selected cut at depth 12, code 105336, node 787978",
                "At remaining fuel 9 and original index 787978, selection on the full partial prefix of depth 12 and code 105336 returns the complete row with depth 12, base-four code 105336, original node 787978, kind 2, reserved field 0, 1353 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-26317-786222", "unmarked_context_11_26317_786222", "Unmarked parent at depth 11, code 26317",
                "The frontier Boolean is false at remaining fuel 10, original node 786222, the whole prefixCache at depth 11 and code 26317, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-26333-787953", "unmarked_context_11_26333_787953", "Unmarked parent at depth 11, code 26333",
                "The frontier Boolean is false at remaining fuel 10, original node 787953, the whole prefixCache at depth 11 and code 26333, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-26317-786222", "node_context_11_26317_786222", "Original split at fuel 10 and node 786222",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 786007, 786092, 786161, 786221. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-26333-787953", "node_context_11_26333_787953", "Original split at fuel 10 and node 787953",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 787875, 787898, 787930, 787952. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-105271-786221", "context_12_105271_786221", "Context at depth 12, code 105271, node 786221",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 105271 and original node 786221, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-105336-787978", "context_12_105336_787978", "Context at depth 12, code 105336, node 787978",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 105336 and original node 787978, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
