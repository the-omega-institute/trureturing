using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1048Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1048.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1048",
        H("Original frontier context coverage 1048"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-50307", "selected_cut_50307", "Selected cut at depth 12, code 424464, node 1415033",
                "At remaining fuel 9 and original index 1415033, selection on the full partial prefix of depth 12 and code 424464 returns the complete row with depth 12, base-four code 424464, original node 1415033, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-50355", "selected_cut_50355", "Selected cut at depth 11, code 106143, node 1437539",
                "At remaining fuel 10 and original index 1437539, selection on the full partial prefix of depth 11 and code 106143 returns the complete row with depth 11, base-four code 106143, original node 1437539, kind 2, reserved field 0, 749 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-106116-1435649", "unmarked_context_11_106116_1435649", "Unmarked parent at depth 11, code 106116",
                "The frontier Boolean is false at remaining fuel 10, original node 1435649, the whole prefixCache at depth 11 and code 106116, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-26535-1437540", "unmarked_context_10_26535_1437540", "Unmarked parent at depth 10, code 26535",
                "The frontier Boolean is false at remaining fuel 11, original node 1437540, the whole prefixCache at depth 10 and code 26535, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-106116-1435649", "node_context_11_106116_1435649", "Original split at fuel 10 and node 1435649",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1415033, 1435515, 1435583, 1435648. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-26535-1437540", "node_context_10_26535_1437540", "Original split at fuel 11 and node 1437540",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1437425, 1437482, 1437520, 1437539. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-424464-1415033", "context_12_424464_1415033", "Context at depth 12, code 424464, node 1415033",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 424464 and original node 1415033, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-26535-1437540", "context_10_26535_1437540", "Context at depth 10, code 26535, node 1437540",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 26535 and original node 1437540, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_106140_1437425, context_11_106141_1437482, context_11_106142_1437520, context_11_106143_1437539.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
