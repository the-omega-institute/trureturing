using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0687Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0687.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0687",
        H("Original frontier context coverage 0687"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-32980", "selected_cut_32980", "Selected cut at depth 13, code 439516, node 848909",
                "At remaining fuel 8 and original index 848909, selection on the full partial prefix of depth 13 and code 439516 returns the complete row with depth 13, base-four code 439516, original node 848909, kind 2, reserved field 0, 313 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-33026", "selected_cut_33026", "Selected cut at depth 12, code 109904, node 850189",
                "At remaining fuel 9 and original index 850189, selection on the full partial prefix of depth 12 and code 109904 returns the complete row with depth 12, base-four code 109904, original node 850189, kind 2, reserved field 0, 3837 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-109879-848998", "unmarked_context_12_109879_848998", "Unmarked parent at depth 12, code 109879",
                "The frontier Boolean is false at remaining fuel 9, original node 848998, the whole prefixCache at depth 12 and code 109879, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-6868-850138", "unmarked_context_10_6868_850138", "Unmarked parent at depth 10, code 6868",
                "The frontier Boolean is false at remaining fuel 11, original node 850138, the whole prefixCache at depth 10 and code 6868, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-109879-848998", "node_context_12_109879_848998", "Original split at fuel 9 and node 848998",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 848909, 848957, 848990, 848997. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-6868-850138", "node_context_10_6868_850138", "Original split at fuel 11 and node 850138",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 849503, 849687, 849928, 850137. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-439516-848909", "context_13_439516_848909", "Context at depth 13, code 439516, node 848909",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 439516 and original node 848909, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-109904-850189", "context_12_109904_850189", "Context at depth 12, code 109904, node 850189",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 109904 and original node 850189, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
