using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1071Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1071.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1071",
        H("Original frontier context coverage 1071"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-51411", "selected_cut_51411", "Selected cut at depth 11, code 280989, node 1482431",
                "At remaining fuel 10 and original index 1482431, selection on the full partial prefix of depth 11 and code 280989 returns the complete row with depth 11, base-four code 280989, original node 1482431, kind 2, reserved field 0, 1829 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-51458", "selected_cut_51458", "Selected cut at depth 11, code 281222, node 1484175",
                "At remaining fuel 10 and original index 1484175, selection on the full partial prefix of depth 11 and code 281222 returns the complete row with depth 11, base-four code 281222, original node 1484175, kind 2, reserved field 0, 1753 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-70247-1482464", "unmarked_context_10_70247_1482464", "Unmarked parent at depth 10, code 70247",
                "The frontier Boolean is false at remaining fuel 11, original node 1482464, the whole prefixCache at depth 10 and code 70247, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-7-1097-1483833", "unmarked_context_7_1097_1483833", "Unmarked parent at depth 7, code 1097",
                "The frontier Boolean is false at remaining fuel 14, original node 1483833, the whole prefixCache at depth 7 and code 1097, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-70247-1482464", "node_context_10_70247_1482464", "Original split at fuel 11 and node 1482464",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1482400, 1482431, 1482463, 1470044. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-7-1097-1483833", "node_context_7_1097_1483833", "Original split at fuel 14 and node 1483833",
                "The complete original decoder output is the split at coordinate 7, with value children 0 through 3 respectively at original indices 14300, 1481637, 1482704, 1483832. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-280989-1482431", "context_11_280989_1482431", "Context at depth 11, code 280989, node 1482431",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 280989 and original node 1482431, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-281222-1484175", "context_11_281222_1484175", "Context at depth 11, code 281222, node 1484175",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 281222 and original node 1484175, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
